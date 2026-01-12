use std::collections::HashMap;

use crate::{CliArgs, sat::{SatInstance, SatLiteral, SatOutcome, SatSolver}};

pub struct ConfigVars<ConfigVarsData> {
  pub config_vars_data: ConfigVarsData,
  pub input_count:      usize,
  pub output_count:     usize,
}

pub trait Program: std::fmt::Debug {
  fn pretty_print(&self) -> String {
    format!("{:?}", self)
  }
}

pub trait ProgramSynthesis: std::fmt::Debug {
  type ConfigVarsData;

  fn create_configuration_vars(
    instance: &mut SatInstance,
    resources: &CliArgs,
  ) -> ConfigVars<Self::ConfigVarsData>;
  fn program_to_bits(
    &self,
    instance: &mut SatInstance,
    resources: &CliArgs,
    false_lit: SatLiteral,
  ) -> ConfigVars<Self::ConfigVarsData>;
  fn decode_program(
    config: &ConfigVars<Self::ConfigVarsData>,
    resources: &CliArgs,
    model: &HashMap<SatLiteral, bool>,
  ) -> Self;
  fn enumerate_vars_in_config(config_vars: &ConfigVars<Self::ConfigVarsData>) -> Vec<SatLiteral>;
  fn evaluate(&self, inputs: &[bool]) -> Vec<bool>;
  fn build_fpga(
    instance: &mut SatInstance,
    resources: &CliArgs,
    configuration_vars: &ConfigVars<Self::ConfigVarsData>,
    input_vars: &[SatLiteral],
    output_vars: &[SatLiteral],
  );
}

pub fn lookup_table_search<OutputSynth: ProgramSynthesis>(
  solver: SatSolver,
  lut: impl Fn(&[bool]) -> Vec<bool>,
  resources_spec: &CliArgs,
  _log: impl Fn(&str),
) -> Option<OutputSynth> {
  let mut program_search_instance = SatInstance::new(solver);
  let config_vars =
    OutputSynth::create_configuration_vars(&mut program_search_instance, resources_spec);

  let false_lit = program_search_instance.fresh();
  program_search_instance.add_clause(vec![-false_lit]);
  let bits_to_literals = |bits: &[bool]| -> Vec<SatLiteral> {
    bits
      .iter()
      .map(|bit| match bit {
        true => -false_lit,
        false => false_lit,
      })
      .collect()
  };

  let mut counter_example_bits = vec![false; config_vars.input_count];
  for i in 0..1 << config_vars.input_count {
    for (j, bit) in counter_example_bits.iter_mut().enumerate() {
      *bit = (i >> j) & 1 == 1;
    }
    let desired_value = lut(&counter_example_bits);
    // Add this input as a constraint on our program search.
    OutputSynth::build_fpga(
      &mut program_search_instance,
      &resources_spec,
      &config_vars,
      &bits_to_literals(&counter_example_bits),
      &bits_to_literals(&desired_value),
    );
  }

  let program_search_model = match program_search_instance.solve() {
    SatOutcome::SAT(model) => model,
    SatOutcome::UNSAT => return None,
  };
  let synthesized_program = OutputSynth::decode_program(
    &config_vars,
    &resources_spec,
    &program_search_model,
  );

  // Do a final check to make sure the synthesized program is correct.
  for input in 0..1 << config_vars.input_count {
    let bits: Vec<bool> = (0..config_vars.input_count).map(|i| (input >> i) & 1 == 1).collect();
    let sop1_value = lut(&bits);
    let sop2_value = OutputSynth::evaluate(&synthesized_program, &bits);
    assert_eq!(sop1_value, sop2_value);
  }

  Some(synthesized_program)
}

// FIXME: Tests!

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{sat::{DEFAULT_SOLVER, cardinality_constraint}};

  #[test]
  fn test_cardinality_constraint() {
    let mut instance = SatInstance::new(DEFAULT_SOLVER);
    let vars = vec![instance.fresh(), instance.fresh(), instance.fresh()];
    cardinality_constraint(&mut instance, &vars, None, 2);
    assert!(matches!(instance.solve(), SatOutcome::SAT(_)));
    instance.add_clause(vec![vars[2]]);
    assert!(matches!(instance.solve(), SatOutcome::SAT(_)));
    instance.add_clause(vec![vars[0]]);
    assert!(matches!(instance.solve(), SatOutcome::SAT(_)));
    instance.add_clause(vec![vars[1]]);
    assert!(matches!(instance.solve(), SatOutcome::UNSAT));
  }

  #[test]
  fn test_vacuous_cardinality_constraint() {
    let mut instance = SatInstance::new(DEFAULT_SOLVER);
    let vars = vec![instance.fresh(), instance.fresh(), instance.fresh()];
    cardinality_constraint(&mut instance, &vars, None, 5);
    assert!(matches!(instance.solve(), SatOutcome::SAT(_)));
  }

  // #[test]
  // fn test_minimize() {
  //   let solver = DEFAULT_SOLVER;
  //   let sop = SumOfProducts(vec![vec![1], vec![2], vec![1, 2]]);
  //   for (limit, has_solution) in [(3, true), (2, true), (1, false)] {
  //     assert_eq!(
  //       program_search::<SumOfProducts, SumOfProducts>(
  //         solver,
  //         &sop,
  //         &SumOfProductsResourcesSpec {
  //           input_count: 2,
  //           term_limit:  limit,
  //         },
  //         &SumOfProductsResourcesSpec {
  //           input_count: 2,
  //           term_limit:  limit,
  //         },
  //         |_| ()
  //       )
  //       .is_some(),
  //       has_solution,
  //     );
  //   }
  // }

  // #[test]
  // fn test_all_solvers() {
  //   //assert!(program_search(SatSolver::External(&["cryptominisat"]), &[vec![1], vec![-1]], 1).is_some());
  //   //assert!(program_search(SatSolver::External(&["glucose", "-model"]), &[vec![1], vec![-1]], 1).is_some());
  //   //assert!(program_search(SatSolver::External(&["kissat"]), &[vec![1], vec![-1]], 1).is_some());
  //   //assert!(program_search(SatSolver::External(&["cadical"]), &[vec![1], vec![-1]], 1).is_some());
  //   assert!(lookup_table_search::<SumOfProducts, SumOfProducts>(
  //     SatSolver::Varisat,
  //     &SumOfProducts(vec![vec![1], vec![-1]]),
  //     &SumOfProductsResourcesSpec {
  //       input_count: 1,
  //       term_limit:  1,
  //     },
  //     &SumOfProductsResourcesSpec {
  //       input_count: 1,
  //       term_limit:  1,
  //     },
  //     |_| (),
  //   )
  //   .is_some());
  //   assert!(lookup_table_search::<SumOfProducts, SumOfProducts>(
  //     SatSolver::Splr,
  //     &SumOfProducts(vec![vec![1], vec![-1]]),
  //     &SumOfProductsResourcesSpec {
  //       input_count: 1,
  //       term_limit:  1,
  //     },
  //     &SumOfProductsResourcesSpec {
  //       input_count: 1,
  //       term_limit:  1,
  //     },
  //     |_| (),
  //   )
  //   .is_some());
  // }
}
