use crate::cpu_instruction::{CPUInstruction, LogLine};
use crate::registers::Registers;
use crate::memory::RAM as Memory;
use crate::addressing_mode::*;

pub fn lda(memory: &mut Memory, registers: &mut Registers, cpu_instruction: &CPUInstruction) -> LogLine {
    let resolution = cpu_instruction.addressing_mode.solve(registers.command_pointer, memory, registers);
    let target_address = match resolution.target_address {
        Some(v) => v,
        None => panic!("Ooops no target address from the addressing mode resolver."),
    };

    registers.accumulator = memory.read(target_address, 1).unwrap()[0];
    registers.command_pointer += 1 + resolution.operands.len();

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
    fn test_lda() {
        let cpu_instruction = CPUInstruction::new(0x1000, 0xca, "LDA", AddressingMode::ZeroPage, lda);
        let (mut memory, mut registers) = get_stuff(0x1000, vec![0xa9, 0x0a]);
        registers.accumulator = 0x10;
        memory.write(0x000a, vec![0xfa]).unwrap();
        let log_line = cpu_instruction.execute(&mut memory, &mut registers);
        assert_eq!("LDA".to_owned(), log_line.mnemonic);
        assert_eq!(0xfa, registers.accumulator);
        assert_eq!(0x1002, registers.command_pointer);
    }
}