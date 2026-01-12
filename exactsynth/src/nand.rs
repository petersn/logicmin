use std::collections::HashMap;

use crate::{CliArgs, sat::{Address, SatInstance, SatLiteral}, synth::{ConfigVars, Program, ProgramSynthesis}};

pub const ALLOW_CONSTANT_INPUTS: bool = false;

fn nand_gate(instance: &mut SatInstance, x0: SatLiteral, x1: SatLiteral) -> SatLiteral {
  let output = instance.fresh();
  instance.add_clause(vec![-output, -x0, -x1]);
  instance.add_clause(vec![output, x0]);
  instance.add_clause(vec![output, x1]);
  output
}

#[derive(Debug, Clone)]
pub struct NandGate {
  pub input_indices: [usize; 2],
}

#[derive(Debug, Clone)]
pub struct NandProgram {
  pub input_count: usize,
  pub output_count: usize,
  pub gates: Vec<NandGate>,
  pub final_selection: Vec<usize>,
}

impl Program for NandProgram {
  fn pretty_print(&self) -> String {
    self.pretty_print()
  }
}

impl NandProgram {
  pub fn pretty_print(&self) -> String {
    let mut s = String::new();
    let format_index = |mut index: usize| {
      if ALLOW_CONSTANT_INPUTS {
        match index {
          0 => return "0".to_string(),
          1 => return "1".to_string(),
          _ => index -= 2,
        }
      }
      if index < self.input_count {
        return format!("\x1b[93mx{}\x1b[0m", index);
      }
      format!("\x1b[92mt{}\x1b[0m", index - self.input_count)
    };
    // s.push_str(&format!("x0, ... x{} = input bits\n", self.input_count - 1));
    s.push_str("def f(");
    for i in 0..self.input_count {
      if i != 0 {
        s.push_str(", ");
      }
      s.push_str(&format!("\x1b[93mx{}\x1b[0m", i));
    }
    s.push_str("):\n");
    for (i, gate) in self.gates.iter().enumerate() {
      s.push_str(&format!("    \x1b[92mt{}\x1b[0m = not ({} and {})\n", i,
        format_index(gate.input_indices[0]),
        format_index(gate.input_indices[1]),
      ));
    }
    s.push_str("    return");
    let maybe_two = if ALLOW_CONSTANT_INPUTS { 2 } else { 0 };
    let just_last = [maybe_two + self.input_count + self.gates.len() - 1];
    let fs: &[usize] = if self.output_count == 1 {
      &just_last
    } else {
      &self.final_selection
    };
    for (i, &final_selection) in fs.iter().enumerate() {
      if i != 0 {
        s.push_str(", ");
      }
      s.push_str(&format!(" {}", format_index(final_selection)));
    }
    s
  }
}

#[derive(Debug)]
pub struct NandResourcesSpec {
  pub input_count: usize,
  pub output_count: usize,
  pub gate_count:  usize,
}

pub struct NandGateConfigVars {
  pub input_indices: [Address; 2],
}

pub struct NandConfigVars {
  pub gates: Vec<NandGateConfigVars>,
  pub final_selection: Vec<Address>,
}

impl ProgramSynthesis for NandProgram {
  type ConfigVarsData = NandConfigVars;

  fn create_configuration_vars(
    instance: &mut SatInstance,
    resources_spec: &CliArgs,
  ) -> ConfigVars<Self::ConfigVarsData> {
    let mut gates = Vec::new();
    let mut wire_count = resources_spec.input_count;
    if ALLOW_CONSTANT_INPUTS {
      wire_count += 2;
    }
    for _ in 0..resources_spec.gate_count {
      let input_indices = [
        Address::make(resources_spec.mux_style, instance, wire_count),
        Address::make(resources_spec.mux_style, instance, wire_count),
      ];
      gates.push(NandGateConfigVars {
        input_indices,
      });
      wire_count += 1;
    }
    let final_selection = if resources_spec.output_count() == 1 {
      Vec::new()
    } else {
      (0..resources_spec.output_count()).map(|_| Address::make(resources_spec.mux_style, instance, wire_count)).collect()
    };
    for constr in &resources_spec.constraints() {
      let addr_to_constrain = if constr.which_gate == gates.len() {
        &final_selection[constr.which_input]
      } else {
        &gates[constr.which_gate].input_indices[constr.which_input]
      };
      addr_to_constrain.constrain_address(instance, constr.where_to_wire);
    }
    ConfigVars {
      config_vars_data: NandConfigVars {
        gates,
        final_selection,
      },
      input_count: resources_spec.input_count,
      output_count: resources_spec.output_count(),
    }
  }

  fn program_to_bits(
    &self,
    _instance: &mut SatInstance,
    resources: &CliArgs,
    false_lit: SatLiteral,
  ) -> ConfigVars<Self::ConfigVarsData> {
    // let bool_to_lit = |b: bool| if b { -false_lit } else { false_lit };
    // let number_to_bits = |number: usize, bits: usize| {
    //   assert!(number < 2usize.pow(bits as u32));
    //   (0..bits).map(|i| bool_to_lit((number >> i) & 1 == 1)).collect()
    // };
    let mut config_vars_data = Vec::new();
    let mut wire_count = self.input_count;
    if ALLOW_CONSTANT_INPUTS {
      wire_count += 2;
    }
    for gate in &self.gates {
      config_vars_data.push(NandGateConfigVars {
        input_indices: [
          // number_to_bits(gate.input_indices[0], bits_for_address(resources.mux_style, wire_count)),
          // number_to_bits(gate.input_indices[1], bits_for_address(resources.mux_style, wire_count)),
          Address::constant_address(resources.mux_style, wire_count, false_lit, gate.input_indices[0]),
          Address::constant_address(resources.mux_style, wire_count, false_lit, gate.input_indices[1]),
        ],
      });
      wire_count += 1;
    }
    let final_selection = if self.output_count == 1 {
      Vec::new()
    } else {
      self.final_selection.iter().map(|&wire_index| {
        // number_to_bits(wire_index, bits_for_address(resources.mux_style, wire_count))
        Address::constant_address(resources.mux_style, wire_count, false_lit, wire_index)
      }).collect()
    };
    ConfigVars {
      config_vars_data: NandConfigVars {
        gates: config_vars_data,
        final_selection,
      },
      input_count: self.input_count,
      output_count: self.output_count,
    }
  }

  fn decode_program(
    config: &ConfigVars<Self::ConfigVarsData>,
    _resources: &CliArgs,
    model: &HashMap<SatLiteral, bool>,
  ) -> Self {
    let mut gates = Vec::new();
    for gate in &config.config_vars_data.gates {
      let input_indices = [
        gate.input_indices[0].decode_address(model),
        gate.input_indices[1].decode_address(model),
      ];
      gates.push(NandGate { input_indices });
    }
    let final_selection = if config.output_count == 1 {
      Vec::new()
    } else {
      config.config_vars_data.final_selection.iter().map(|addr| addr.decode_address(model)).collect()
    };
    NandProgram {
      input_count: config.input_count,
      output_count: config.output_count,
      gates,
      final_selection,
    }
  }

  fn enumerate_vars_in_config(config_vars: &ConfigVars<Self::ConfigVarsData>) -> Vec<SatLiteral> {
    let mut vars = Vec::new();
    for gate in &config_vars.config_vars_data.gates {
      for input_indices in &gate.input_indices {
        vars.extend_from_slice(&input_indices.address);
      }
    }
    for final_selection in &config_vars.config_vars_data.final_selection {
      vars.extend_from_slice(&final_selection.address);
    }
    vars
  }

  fn evaluate(&self, inputs: &[bool]) -> Vec<bool> {
    let mut values = inputs.to_vec();
    if ALLOW_CONSTANT_INPUTS {
      values.insert(0, false);
      values.insert(1, true);
    }
    for gate in &self.gates {
      let x0 = values.get(gate.input_indices[0]).copied().unwrap_or(false);
      let x1 = values.get(gate.input_indices[1]).copied().unwrap_or(false);
      values.push(!(x0 && x1));
    }
    if self.output_count == 1 {
      return vec![values.last().copied().unwrap_or(false)];
    }
    (0..self.output_count).map(|i| values.get(self.final_selection[i]).copied().unwrap_or(false)).collect()
  }

  fn build_fpga(
    instance: &mut SatInstance,
    _resources: &CliArgs,
    configuration_vars: &ConfigVars<Self::ConfigVarsData>,
    input_vars: &[SatLiteral],
    output_vars: &[SatLiteral],
  ) {
    assert_eq!(input_vars.len(), configuration_vars.input_count);
    assert_eq!(output_vars.len(), configuration_vars.output_count);
    let false_lit = instance.fresh();
    instance.add_clause(vec![-false_lit]);
    let mut wires = input_vars.to_vec();
    if ALLOW_CONSTANT_INPUTS {
      wires.insert(0, false_lit);
      wires.insert(1, -false_lit);
    }
    for gate in &configuration_vars.config_vars_data.gates {
      // let x0 = mux(resources.mux_style, instance, &gate.input_indices[0], &wires);
      // let x1 = mux(resources.mux_style, instance, &gate.input_indices[1], &wires);
      let x0 = gate.input_indices[0].mux(instance, &wires);
      let x1 = gate.input_indices[1].mux(instance, &wires);
      let lut_output = nand_gate(instance, x0, x1);
      wires.push(lut_output);
    }
    if configuration_vars.output_count == 1 {
      let final_bit = *wires.last().unwrap();
      instance.add_clause(vec![final_bit, -output_vars[0]]);
      instance.add_clause(vec![-final_bit, output_vars[0]]);
    } else {
      for i in 0..configuration_vars.output_count {
        //let final_bit = mux(resources.mux_style, instance, &configuration_vars.config_vars_data.final_selection[i], &wires);
        let final_bit = configuration_vars.config_vars_data.final_selection[i].mux(instance, &wires);
        instance.add_clause(vec![final_bit, -output_vars[i]]);
        instance.add_clause(vec![-final_bit, output_vars[i]]);
      }
    }
  }
}
