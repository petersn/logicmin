pub mod sat_tables;
pub mod sum_of_products;
pub mod luts;
pub mod nand;
pub mod synth;
pub mod sat;

use clap::Parser;
use luts::LutProgram;
use nand::NandProgram;
use num_bigint::BigUint;
use sat::{MuxStyle, SatSolver};
use sum_of_products::SumOfProducts;
use synth::{Program, lookup_table_search};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExtraConstraint {
  pub which_gate: usize,
  pub which_input: usize,
  pub where_to_wire: usize,
}

#[derive(clap::ValueEnum, Clone, Debug)]
pub enum ProgramKind {
  BinaryGates,
  TernaryGates,
  QuaternaryGates,
  NandGates,
  SumOfProducts,
}

#[derive(Debug, Parser)]
#[command(version, about, long_about = None)]
pub struct CliArgs {
  #[arg(short, long)]
  kind: ProgramKind,

  #[arg(short, long)]
  input_count: usize,

  #[arg(short, long)]
  luts: Vec<String>,

  #[arg(short, long)]
  gate_count: usize,

  #[arg(short, long, default_value = "cryptominisat5")]
  solver: String,

  #[arg(short, long, default_value = "[]")]
  constraints: String,

  #[arg(long, default_value="one-hot")]
  mux_style: MuxStyle,
}

impl CliArgs {
  fn output_count(&self) -> usize {
    self.luts.len()
  }

  fn constraints(&self) -> Vec<ExtraConstraint> {
    let constraints: Vec<(usize, usize, usize)> = serde_json::from_str(&self.constraints).unwrap();
    constraints.into_iter().map(|(a, b, c)| ExtraConstraint {
      which_gate: a,
      which_input: b,
      where_to_wire: c,
    }).collect()
  }
}

fn parse_biguint(s: &str) -> Option<BigUint> {
  if let Some(hex) = s.strip_prefix("0x") {
    BigUint::parse_bytes(hex.as_bytes(), 16)
  } else {
    BigUint::parse_bytes(s.as_bytes(), 10)
  }
}

fn main() {
  let cli_args = CliArgs::parse();
  let luts: Vec<BigUint> = cli_args.luts.iter().map(|s| parse_biguint(s).unwrap()).collect();
  for lut in &luts {
    let max_value = (BigUint::from(1u64) << (1 << cli_args.input_count)) - BigUint::from(1u64);
    if *lut > max_value {
      eprintln!("LUT value is too large for input count: 0x{:x}. Maximum sensible value: 0x{:x}", lut, max_value);
      std::process::exit(1);
    }
  }
  let solver_string: &'static str = Box::leak(cli_args.solver.clone().into_boxed_str());
  let solver_cmd: &'static [&'static str] = Box::leak(Box::new([solver_string]));
  let solver = SatSolver::External(solver_cmd);

  let f = |bits: &[bool]| {
    let value = bits.iter().enumerate().map(|(i, &b)| if b { 1 << i } else { 0 }).sum::<usize>();
    let mut r = Vec::new();
    for lut in &luts {
      r.push(lut.bit(value as u64));
    }
    r
  };
  let log = |msg: &str| {
    println!("[{:?}] {}", solver, msg);
  };

  let p: Option<Box<dyn Program>> = match cli_args.kind {
    ProgramKind::BinaryGates => match lookup_table_search::<LutProgram<2, 4>>(
      solver, f, &cli_args, log,
    ) {
      None => None, Some(x) => Some(Box::new(x)),
    }
    ProgramKind::TernaryGates => match lookup_table_search::<LutProgram<3, 8>>(
      solver, f, &cli_args, log,
    ) {
      None => None, Some(x) => Some(Box::new(x)),
    }
    ProgramKind::QuaternaryGates => match lookup_table_search::<LutProgram<4, 16>>(
      solver, f, &cli_args, log,
    ) {
      None => None, Some(x) => Some(Box::new(x)),
    }
    ProgramKind::NandGates => match lookup_table_search::<NandProgram>(
      solver, f, &cli_args, log,
    ) {
      None => None, Some(x) => Some(Box::new(x)),
    }
    ProgramKind::SumOfProducts => match lookup_table_search::<SumOfProducts>(
      solver, f, &cli_args, log,
    ) {
      None => None, Some(x) => Some(Box::new(x)),
    }
  };

  match p {
    None => eprintln!("No program found."),
    Some(p) => eprintln!("{}", p.pretty_print()),
  }
}
