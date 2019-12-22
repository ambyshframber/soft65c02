use crate::cpu_instruction::{CPUInstruction, LogLine};
use crate::registers::Registers;
use crate::memory::RAM as Memory;
use crate::addressing_mode::*;

pub fn brk(memory: &mut Memory, registers: &mut Registers, cpu_instruction: &CPUInstruction) -> LogLine {
    let resolution = cpu_instruction.addressing_mode.solve(registers.command_pointer, memory, registers);
    let _target_address:Option<usize> = match resolution.target_address {
        Some(v) => panic!("Address resolver must NOT give us any address."),
        None => None,
    };

    LogLine {
        address:    cpu_instruction.address,
        opcode:     cpu_instruction.opcode,
        mnemonic:   cpu_instruction.mnemonic.clone(),
        resolution: resolution,
        is_simulated: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu_instruction::cpu_instruction::tests::get_stuff;

    #[test]
    fn test_brk() {
        let cpu_instruction = CPUInstruction::new(0x1000, 0xca, "BRK", AddressingMode::Implied, brk);
        let (mut memory, mut registers) = get_stuff(0x1000, vec![0xca, 0x0a, 0x02]);
        let log_line = cpu_instruction.execute(&mut memory, &mut registers);
        assert_eq!("BRK".to_owned(), log_line.mnemonic);
        assert_eq!(0x1000, registers.command_pointer);
    }
}