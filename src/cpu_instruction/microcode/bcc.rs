use super::*;

pub fn bcc(memory: &mut Memory, registers: &mut Registers, cpu_instruction: &CPUInstruction) -> Result<LogLine> {
    let resolution = cpu_instruction.addressing_mode
        .solve(registers.command_pointer, memory, registers)?;
    let target_address = resolution.target_address
        .expect("BCC must have operands, crashing the application");

    if registers.c_flag_is_set() {
        registers.command_pointer += 1 + resolution.operands.len();
    } else {
        registers.command_pointer = target_address;
    }

    Ok(LogLine::new(&cpu_instruction, resolution, format!("[CP=0x{:04X}]", registers.command_pointer)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu_instruction::cpu_instruction::tests::get_stuff;

    #[test]
    fn test_bcc() {
        let cpu_instruction = CPUInstruction::new(0x1000, 0xca, "BCC", AddressingMode::Relative([0x0a]), bcc);
        let (mut memory, mut registers) = get_stuff(0x1000, vec![0xe8, 0x0a, 0x02]);
        registers.set_c_flag(true);
        let log_line = cpu_instruction.execute(&mut memory, &mut registers).unwrap();
        assert_eq!("BCC".to_owned(), log_line.mnemonic);
        assert!(registers.c_flag_is_set());
        assert_eq!(0x1002, registers.command_pointer);
    }

    #[test]
    fn test_bcc_with_c_clear() {
        let cpu_instruction = CPUInstruction::new(0x1000, 0xca, "BCC", AddressingMode::Relative([0x0a]), bcc);
        let (mut memory, mut registers) = get_stuff(0x1000, vec![0xe8, 0x0a, 0x02]);
        registers.set_c_flag(false);
        let log_line = cpu_instruction.execute(&mut memory, &mut registers).unwrap();
        assert!(!registers.c_flag_is_set());
        assert_eq!(0x100c, registers.command_pointer);
    }
}

