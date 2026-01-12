use std::collections::{HashMap, HashSet};

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
  log: impl Fn(&str),
) -> Option<OutputSynth> {
  let mut program_search_instance = SatInstance::new(solver);
  let config_vars =
    OutputSynth::create_configuration_vars(&mut program_search_instance, resources_spec);
  //// Constrain cost.
  //OutputSynth::constrain_cost(&mut program_search_instance, &config_vars_data, cost_limit);

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

  // Construct a template SAT instance to use for counter-example search.
  let mut counter_examples = HashSet::new();
  // let mut counter_example_search_template = program_search_instance.clone();
  // let counter_example_search_inputs =
  //   counter_example_search_template.n_fresh(config_vars.input_count);
  // {
  //   // Build the circuitry that computes the original program for testing against.
  //   let reference_output = counter_example_search_template.n_fresh(config_vars.output_count);
  //   let test_output = counter_example_search_template.n_fresh(config_vars.output_count);
  //   let base_program_cfg_vars = base_program.program_to_bits(&mut counter_example_search_template, false_lit);
  //   InputSynth::build_fpga(
  //     &mut counter_example_search_template,
  //     &base_program_cfg_vars,
  //     &counter_example_search_inputs,
  //     &reference_output,
  //   );
  //   // Build circuitry that tests out the candidate program.
  //   OutputSynth::build_fpga(
  //     &mut counter_example_search_template,
  //     &config_vars,
  //     &counter_example_search_inputs,
  //     &test_output,
  //   );
  //   // Demand that the outputs disagree (as we're searching for a counter-example).
  //   force_unequal(&mut counter_example_search_template, &reference_output, &test_output);
  // }

  let minimized_program = loop {
    // === Step 1: Search for a program that agrees with the original program on all counter-examples.
    let program_search_model = match program_search_instance.solve() {
      SatOutcome::SAT(model) => model,
      SatOutcome::UNSAT => return None,
    };

    // // Take our counter-example search template, and assign the selection
    // // variables to configure it to test the program we just found.
    // let mut counter_example_search_instance = counter_example_search_template.clone();
    // for var in OutputSynth::enumerate_vars_in_config(&config_vars) {
    //   let bit = program_search_model.get(&var).copied().unwrap_or(false);
    //   counter_example_search_instance.add_clause(match bit {
    //     true => vec![var],
    //     false => vec![-var],
    //   });
    // }

    let candidate_program = OutputSynth::decode_program(
      &config_vars,
      &resources_spec,
      &program_search_model,
    );
    let mut bits = vec![false; config_vars.input_count];
    // let mut counter_example = None;
    let mut current_counter_examples = Vec::new();
    for i in 0..1 << config_vars.input_count {
      for (j, bit) in bits.iter_mut().enumerate() {
        *bit = (i >> j) & 1 == 1;
      }
      let sop1_value = lut(&bits);
      let sop2_value = OutputSynth::evaluate(&candidate_program, &bits);
      if sop1_value != sop2_value {
        //panic!("Disagreement: {:?} vs {:?}", sop1_value, sop2_value);
        // counter_example = Some(bits.clone());
        // break;
        // counter_example_count += 1;
        current_counter_examples.push(bits.clone());
      }
    }

    if current_counter_examples.is_empty() {
      break candidate_program;
    }

    // InputSynth::fix_configuration(
    //   &mut counter_example_search_instance,
    //   &program_search_model,
    //   &InputSynth::program_to_bits(
    //     &mut counter_example_search_instance,
    //     false_lit,
    //     base_program,
    //   ),
    // );
    // let mut candidate_program = Vec::new();
    // for configuration_var in &configuration_vars {
    //   let bit = program_search_model.get(&configuration_var).copied().unwrap_or(false);
    //   candidate_program.push(bit);
    //   counter_example_search_instance.add_clause(match bit {
    //     true => vec![*configuration_var],
    //     false => vec![-*configuration_var],
    //   });
    // }
    // log(&format!(
    //   "Found candidate program: {:?}",
    //   OutputSynth::bits_to_program(input_vars.len(), &candidate_program),
    // ));

    // // === Step 2: Find a counter-example where the candidate program disagrees with the original.
    // let counter_example_model = match counter_example_search_instance.solve() {
    //   SatOutcome::SAT(model) => model,
    //   // If no counter-example exists, then we have found a minimized program.
    //   SatOutcome::UNSAT => break OutputSynth::decode_program(&config_vars, &program_search_model),
    // };


    // let mut counter_example_bits = vec![];
    // Force the inputs.
    let correct_behavior = (1 << config_vars.input_count) - current_counter_examples.len();
    log(&format!("[{} examples] [correct behavior: {}/{}]",
      counter_examples.len(), correct_behavior, 1 << config_vars.input_count,
    ));
    // let i = rand::random::<usize>() % current_counter_examples.len();
    // let counter_example_bits = &current_counter_examples[i];
    // Shuffle the current counter-examples.
    let mut rng = rand::thread_rng();
    use rand::seq::SliceRandom;
    current_counter_examples.shuffle(&mut rng);
    // let c = settings.counter_examples_per_step.min(current_counter_examples.len());
    // FIXME: This is broken!
    let c = current_counter_examples.len();
    for counter_example_bits in &current_counter_examples[0..c] {
      if !counter_examples.insert(counter_example_bits.clone()) {
        panic!("Duplicate counter-example: {:?} -- this usually indicates a bug in build_fpga", counter_example_bits);
      }
      let desired_value = lut(&counter_example_bits);
      // Add the counter-example as a constraint on our program search.
      OutputSynth::build_fpga(
        &mut program_search_instance,
        &resources_spec,
        &config_vars,
        &bits_to_literals(&counter_example_bits),
        &bits_to_literals(&desired_value),
      );
    }
  };

  for input in 0..1 << config_vars.input_count {
    let bits: Vec<bool> = (0..config_vars.input_count).map(|i| (input >> i) & 1 == 1).collect();
    let sop1_value = lut(&bits);
    let sop2_value = OutputSynth::evaluate(&minimized_program, &bits);
    // println!("{}: ref={:?} vs minimized={:?}", input, sop1_value, sop2_value);
    assert_eq!(sop1_value, sop2_value);
  }

  Some(minimized_program)
}

// FIXME: Tests!

// #[cfg(test)]
// mod tests {
//   use super::*;
//   use crate::sum_of_products::{SumOfProducts, SumOfProductsResourcesSpec};

//   #[test]
//   fn test_cardinality_constraint() {
//     let mut instance = SatInstance::new(DEFAULT_SOLVER);
//     let vars = vec![instance.fresh(), instance.fresh(), instance.fresh()];
//     cardinality_constraint(&mut instance, &vars, None, 2);
//     assert!(matches!(instance.solve(), SatOutcome::SAT(_)));
//     instance.add_clause(vec![vars[2]]);
//     assert!(matches!(instance.solve(), SatOutcome::SAT(_)));
//     instance.add_clause(vec![vars[0]]);
//     assert!(matches!(instance.solve(), SatOutcome::SAT(_)));
//     instance.add_clause(vec![vars[1]]);
//     assert!(matches!(instance.solve(), SatOutcome::UNSAT));
//   }

//   #[test]
//   fn test_vacuous_cardinality_constraint() {
//     let mut instance = SatInstance::new(DEFAULT_SOLVER);
//     let vars = vec![instance.fresh(), instance.fresh(), instance.fresh()];
//     cardinality_constraint(&mut instance, &vars, None, 5);
//     assert!(matches!(instance.solve(), SatOutcome::SAT(_)));
//   }

//   #[test]
//   fn test_minimize() {
//     let solver = DEFAULT_SOLVER;
//     let sop = SumOfProducts(vec![vec![1], vec![2], vec![1, 2]]);
//     for (limit, has_solution) in [(3, true), (2, true), (1, false)] {
//       assert_eq!(
//         program_search::<SumOfProducts, SumOfProducts>(
//           solver,
//           &sop,
//           &SumOfProductsResourcesSpec {
//             input_count: 2,
//             term_limit:  limit,
//           },
//           &SumOfProductsResourcesSpec {
//             input_count: 2,
//             term_limit:  limit,
//           },
//           |_| ()
//         )
//         .is_some(),
//         has_solution,
//       );
//     }
//   }

//   #[test]
//   fn test_all_solvers() {
//     //assert!(program_search(SatSolver::External(&["cryptominisat"]), &[vec![1], vec![-1]], 1).is_some());
//     //assert!(program_search(SatSolver::External(&["glucose", "-model"]), &[vec![1], vec![-1]], 1).is_some());
//     //assert!(program_search(SatSolver::External(&["kissat"]), &[vec![1], vec![-1]], 1).is_some());
//     //assert!(program_search(SatSolver::External(&["cadical"]), &[vec![1], vec![-1]], 1).is_some());
//     assert!(program_search::<SumOfProducts, SumOfProducts>(
//       SatSolver::Varisat,
//       &SumOfProducts(vec![vec![1], vec![-1]]),
//       &SumOfProductsResourcesSpec {
//         input_count: 1,
//         term_limit:  1,
//       },
//       &SumOfProductsResourcesSpec {
//         input_count: 1,
//         term_limit:  1,
//       },
//       |_| (),
//     )
//     .is_some());
//     assert!(program_search::<SumOfProducts, SumOfProducts>(
//       SatSolver::Splr,
//       &SumOfProducts(vec![vec![1], vec![-1]]),
//       &SumOfProductsResourcesSpec {
//         input_count: 1,
//         term_limit:  1,
//       },
//       &SumOfProductsResourcesSpec {
//         input_count: 1,
//         term_limit:  1,
//       },
//       |_| ()
//     )
//     .is_some());
//   }
// }
