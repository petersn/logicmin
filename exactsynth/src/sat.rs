use std::{collections::HashMap, io::Write};

use splr::{SatSolverIF, SolveIF};
use varisat::ExtendFormula;

use crate::sat_tables::StaticCnf;

#[derive(Debug, Clone, Copy)]
pub enum SatSolver {
  External(&'static [&'static str]),
  Varisat,
  Splr,
}

pub const DEFAULT_SOLVER: SatSolver = SatSolver::Splr;

pub type SatLiteral = i32;

pub enum SatOutcome {
  SAT(HashMap<SatLiteral, bool>),
  UNSAT,
}

enum SolverState {
  External(&'static [&'static str]),
  Varisat {
    lits:           Vec<varisat::Lit>,
    varisat_solver: varisat::solver::Solver<'static>,
  },
  Splr {
    empty_clause_inserted: bool,
    splr_solver:           splr::Solver,
  },
}

macro_rules! add_varisat_clause {
  ($lits:expr, $varisat_solver:expr, $clause:expr) => {{
    let clause: Vec<_> = $clause
      .iter()
      .map(|lit| match *lit > 0 {
        true => $lits[*lit as usize - 1],
        false => !$lits[(-*lit) as usize - 1],
      })
      .collect();
    $varisat_solver.add_clause(&clause);
  }};
}

pub struct SatInstance {
  contents:     Vec<Vec<SatLiteral>>,
  current_var:  i32,
  solver_state: SolverState,
}

impl Clone for SatInstance {
  fn clone(&self) -> Self {
    Self {
      contents:     self.contents.clone(),
      current_var:  self.current_var,
      solver_state: match &self.solver_state {
        SolverState::External(command) => SolverState::External(command),
        SolverState::Varisat { .. } => {
          let mut varisat_solver = varisat::solver::Solver::new();
          let lits: Vec<_> = (0..self.current_var).map(|_| varisat_solver.new_lit()).collect();
          for clause in &self.contents {
            add_varisat_clause!(lits, varisat_solver, clause);
          }
          SolverState::Varisat {
            lits,
            varisat_solver,
          }
        }
        SolverState::Splr {
          empty_clause_inserted,
          splr_solver,
        } => SolverState::Splr {
          empty_clause_inserted: *empty_clause_inserted,
          splr_solver:           splr_solver.clone(),
        },
      },
    }
  }
}

impl SatInstance {
  pub fn new(sat_solver: SatSolver) -> Self {
    Self {
      contents:     vec![],
      current_var:  0,
      solver_state: match sat_solver {
        SatSolver::External(command) => SolverState::External(command),
        SatSolver::Varisat => SolverState::Varisat {
          lits:           vec![],
          varisat_solver: varisat::solver::Solver::new(),
        },
        SatSolver::Splr => {
          let empty_instance: &[Vec<i32>] = &[];
          SolverState::Splr {
            empty_clause_inserted: false,
            splr_solver:           splr::Solver::try_from((
              splr::Config::default(),
              empty_instance,
            ))
            .unwrap(),
          }
        }
      },
    }
  }

  pub fn fresh(&mut self) -> SatLiteral {
    self.current_var += 1;
    self.current_var
  }

  pub fn n_fresh(&mut self, n: usize) -> Vec<SatLiteral> {
    (0..n).map(|_| self.fresh()).collect()
  }

  pub fn add_clause(&mut self, clause: Vec<SatLiteral>) {
    match &mut self.solver_state {
      SolverState::External(_) => {}
      SolverState::Varisat {
        lits,
        varisat_solver,
      } => {
        while lits.len() < self.current_var as usize {
          lits.push(varisat_solver.new_lit());
        }
        add_varisat_clause!(lits, varisat_solver, &clause);
      }
      SolverState::Splr {
        empty_clause_inserted,
        splr_solver,
      } => {
        while splr_solver.asg.num_vars < self.current_var as usize {
          splr_solver.add_var();
        }
        match splr_solver.add_clause(&clause) {
          Ok(_) => {}
          // For some weird reason splr doesn't like empty clauses, rather than just giving UNSAT.
          Err(splr::SolverError::EmptyClause) => *empty_clause_inserted = true,
          Err(e) => panic!("Unexpected error: {:?}", e),
        }
      }
    }
    self.contents.push(clause);
  }

  pub fn add_precompiled(
    &mut self,
    template: &StaticCnf,
    inputs: &[SatLiteral],
    outputs: &[SatLiteral],
  ) {
    assert_eq!(inputs.len(), template.input_count);
    assert_eq!(outputs.len(), template.output_count);
    let all_bits: Vec<_> = inputs.iter().chain(outputs.iter()).copied().collect();
    for clause in template.cnf {
      let mut new_clause = vec![];
      for &lit in *clause {
        match lit > 0 {
          true => new_clause.push(all_bits[lit as usize - 1]),
          false => new_clause.push(-all_bits[(-lit) as usize - 1]),
        }
      }
      self.add_clause(new_clause);
    }
  }

  pub fn write_dimacs(&self, file: &mut impl Write) {
    writeln!(file, "p cnf {} {}", self.current_var, self.contents.len()).unwrap();
    for clause in &self.contents {
      for lit in clause {
        write!(file, "{} ", lit).unwrap();
      }
      writeln!(file, "0").unwrap();
    }
  }

  fn solve_external(current_var: i32, clauses: &[Vec<SatLiteral>], command: &[&str]) -> SatOutcome {
    // Create a temporary DIMACS file.
    let file = tempfile::NamedTempFile::new().expect("Failed to create temporary file");
    let temp_path = file.path().to_owned();
    // let mut file = std::fs::File::create("/tmp/test.dimacs").unwrap();
    let mut writer = std::io::BufWriter::new(file);
    // FIXME: Deduplicate this.
    writeln!(writer, "p cnf {} {}", current_var, clauses.len()).unwrap();
    for clause in clauses {
      for lit in clause {
        write!(writer, "{} ", lit).unwrap();
      }
      writeln!(writer, "0").unwrap();
    }
    writer.flush().unwrap();
    // Invoke SAT solver.
    let output = std::process::Command::new(command[0])
      .args(&command[1..])
      .arg(temp_path)
      // .arg("/tmp/test.dimacs")
      .output()
      .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    // Parse output.
    let mut model: HashMap<SatLiteral, bool> = HashMap::new();
    let mut s_line = false;
    for line in stdout.lines() {
      if line.trim().is_empty() {
        continue;
      }
      if line.starts_with("c ") || line == "c" {
        continue;
      } else if line.starts_with("s ") {
        assert!(!s_line);
        s_line = true;
        let mut parts = line.split_whitespace();
        parts.next();
        let status = parts.next().unwrap();
        if status == "UNSATISFIABLE" {
          return SatOutcome::UNSAT;
        }
        assert_eq!(status, "SATISFIABLE");
      } else if line.starts_with("v ") {
        let mut parts = line.split_whitespace();
        parts.next();
        for part in parts {
          let lit = part.parse::<SatLiteral>().unwrap();
          model.insert(lit.abs(), lit > 0);
        }
      } else if s_line {
        // Disallow unknown output after the s line.
        eprintln!("stdout: {}", stdout);
        panic!("Unexpected solver output: {}", line);
      }
    }
    if !s_line {
      eprintln!("stdout: {}", stdout);
      panic!("No s line in solver output");
    }
    SatOutcome::SAT(model)
  }

  fn solve_varisat(varisat_solver: &mut varisat::Solver) -> SatOutcome {
    if !varisat_solver.solve().unwrap() {
      return SatOutcome::UNSAT;
    }
    SatOutcome::SAT(
      varisat_solver
        .model()
        .unwrap()
        .iter()
        .map(|lit| (lit.to_dimacs().abs() as i32, lit.is_positive()))
        .collect(),
    )
  }

  fn solve_splr(splr_solver: &mut splr::Solver) -> SatOutcome {
    let outcome = match splr_solver.solve().unwrap() {
      splr::Certificate::SAT(x) =>
        SatOutcome::SAT(x.iter().map(|&lit| (lit.abs(), lit > 0)).collect()),
      splr::Certificate::UNSAT => SatOutcome::UNSAT,
    };
    // FIXME: Should I be calling reset here?
    //splr_solver.reset();
    outcome
  }

  pub fn solve(&mut self) -> SatOutcome {
    match &mut self.solver_state {
      SolverState::External(command) =>
        SatInstance::solve_external(self.current_var, &self.contents, command),
      SolverState::Varisat { varisat_solver, .. } => SatInstance::solve_varisat(varisat_solver),
      SolverState::Splr {
        empty_clause_inserted: true,
        ..
      } => SatOutcome::UNSAT,
      SolverState::Splr { splr_solver, .. } => SatInstance::solve_splr(splr_solver),
    }
  }
}

pub fn cardinality_constraint(
  instance: &mut SatInstance,
  vars: &[SatLiteral],
  // FIXME: Weights aren't used yet.
  weights: Option<&[usize]>,
  max_count: usize,
) {
  // FIXME: Weights aren't implemented yet.
  assert!(weights.is_none());
  let total_cost_of_all_vars = weights.map(|w| w.iter().sum()).unwrap_or(vars.len());
  if max_count >= total_cost_of_all_vars {
    return;
  }
  if max_count == 0 {
    // Simply set each var to false.
    for var in vars {
      instance.add_clause(vec![-*var]);
    }
    return;
  }
  // at_least_k[(i, k)] is true iff vars[:i] has at least k true literals.
  let mut at_most_k: HashMap<(usize, usize), SatLiteral> = HashMap::new();
  let mut get_var = |instance: &mut SatInstance, i: usize, k: usize| -> SatLiteral {
    *at_most_k.entry((i, k)).or_insert_with(|| instance.fresh())
  };
  let get_weight = |i: usize| weights.map(|w| w[i]).unwrap_or(1);
  for prefix_len in 1..=vars.len() {
    for count in 1..=prefix_len.min(max_count + 1) {
      let here = get_var(instance, prefix_len, count);
      // If we already have `count` true literals at the previous position, we do here too.
      if prefix_len > count {
        let clause = vec![-get_var(instance, prefix_len - 1, count), here];
        instance.add_clause(clause);
      }
      // If we have `count - 1` true literals at the previous position, and
      // the current position is also true, then we have `count` true here.
      if prefix_len == 1 {
        // Simply equate.
        instance.add_clause(vec![-vars[0], here]);
        instance.add_clause(vec![vars[0], -here]);
      } else {
        let clause = match count {
          1 => vec![-vars[prefix_len - 1], here],
          _ => vec![
            -get_var(instance, prefix_len - 1, count - 1),
            -vars[prefix_len - 1],
            here,
          ],
        };
        instance.add_clause(clause);
      }
    }
  }
  // Constrain the final bit to be false.
  let clause = vec![-get_var(instance, vars.len(), max_count + 1)];
  instance.add_clause(clause);
}

fn force_unequal(instance: &mut SatInstance, a: &[SatLiteral], b: &[SatLiteral]) {
  assert!(a.len() == b.len());
  let unequal = instance.n_fresh(a.len());
  for i in 0..a.len() {
    // Add the constraint (a[i] == b[i]) -> !unequal[i]
    instance.add_clause(vec![a[i], b[i], -unequal[i]]);
    instance.add_clause(vec![-a[i], -b[i], -unequal[i]]);
  }
  // Constrain at least one position to be unequal.
  instance.add_clause(unequal);
}

#[derive(clap::ValueEnum, Debug, Copy, Clone, PartialEq, Eq)]
pub enum MuxStyle {
  Binary,
  OneHot,
}

pub fn bits_for_address(style: MuxStyle, options: usize) -> usize {
  match style {
    MuxStyle::Binary => options.next_power_of_two().trailing_zeros() as usize,
    MuxStyle::OneHot => options,
  }
}

pub struct Address {
  pub style: MuxStyle,
  pub options: usize,
  pub address: Vec<SatLiteral>,
}

impl Address {
  pub fn make(style: MuxStyle, instance: &mut SatInstance, options: usize) -> Self {
    let address = instance.n_fresh(bits_for_address(style, options));
    match style {
      MuxStyle::Binary => {
        // No constraints on binary addresses when created.
        // I could add constraints if `options` isn't a power of two, but still.
      }
      MuxStyle::OneHot => {
        // For each pair of address bits, they can't both be true.
        for (i, &a) in address.iter().enumerate() {
          for &b in &address[..i] {
            instance.add_clause(vec![-a, -b]);
          }
        }
        // Assert that at least one address bit is true.
        instance.add_clause(address.iter().copied().collect());
      }
    }
    Address { style, options, address }
  }

  pub fn decode_address(&self, model: &HashMap<SatLiteral, bool>) -> usize {
    let bits: Vec<bool> = self.address.iter().map(|lit| model[lit]).collect();
    assert_eq!(bits.len(), self.address.len());
    match self.style {
      MuxStyle::Binary => bits.iter().enumerate().map(|(i, b)| if *b { 1 << i } else { 0 }).sum(),
      MuxStyle::OneHot => {
        let mut ret = None;
        for (i, b) in bits.iter().enumerate() {
          match (b, ret) {
            (false, _) => {}
            (true, None) => ret = Some(i),
            (true, Some(_)) => panic!("Got more than one hot bit"),
          }
        }
        ret.expect("Didn't find any hot bits")
      }
    }
  }

  pub fn constant_address(style: MuxStyle, options: usize, false_lit: SatLiteral, addr_value: usize) -> Address {
    assert!(addr_value < options);
    let address_len = bits_for_address(style, options);
    let address: Vec<SatLiteral> = match style {
      MuxStyle::Binary => (0..address_len).map(|i| {
        match ((addr_value >> i) & 1) == 1 {
          false => false_lit,
          true => -false_lit,
        }
      }).collect(),
      MuxStyle::OneHot => (0..address_len).map(|i| {
        match addr_value == i {
          false => false_lit,
          true => -false_lit,
        }
      }).collect(),
    };
    assert_eq!(address.len(), address_len);
    Address {
      style,
      options,
      address,
    }
  }

  pub fn constrain_address(&self, instance: &mut SatInstance, addr_value: usize) {
    let const_addr = Self::constant_address(self.style, self.options, -1000, addr_value);
    assert_eq!(const_addr.address.len(), self.address.len());
    for (&fakeo_lit, &real_lit) in const_addr.address.iter().zip(self.address.iter()) {
      match fakeo_lit {
        -1000 => instance.add_clause(vec![-real_lit]),
        1000 => instance.add_clause(vec![real_lit]),
        _ => unreachable!(),
      }
    }
  }

  pub fn mux(
    &self, instance: &mut SatInstance, inputs: &[SatLiteral],
  ) -> SatLiteral {
    assert_eq!(inputs.len(), self.options);
    match self.style {
      MuxStyle::Binary => binary_mux(instance, &self.address, inputs),
      MuxStyle::OneHot => one_hot_mux(instance, &self.address, inputs),
    }
  }
}

pub fn one_hot_mux(
  instance: &mut SatInstance, address: &[SatLiteral], inputs: &[SatLiteral],
) -> SatLiteral {
  let output = instance.fresh();
  for (&addr, &inp) in address.iter().zip(inputs.iter()) {
    // If this address bit is true then the two input bits are equated.
    instance.add_clause(vec![-addr, -inp, output]);
    instance.add_clause(vec![-addr, inp, -output]);
  }
  output
}

pub fn binary_mux(
  instance: &mut SatInstance, address: &[SatLiteral], inputs: &[SatLiteral],
) -> SatLiteral {
  let output = instance.fresh();

  for address_value in 0..1 << address.len() {
    for flip in [-1, 1] {
      let mut clause = if address_value < inputs.len() {
        vec![-flip * inputs[address_value], flip * output]
      } else if flip == -1 {
        continue;
      } else {
        Vec::new()
      };
      for (i, &lit) in address.iter().enumerate() {
        // Note the negation here -- in a Horn clause the condition is negated.
        if (address_value >> i) & 1 == 1 {
          clause.push(-lit);
        } else {
          clause.push(lit);
        }
      }
      instance.add_clause(clause);
    }
  }

  output
}
