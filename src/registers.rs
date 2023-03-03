//! 65C02 registers
//! accumulator, X & Y registers are 8 bits general purpose registers.
//! status flags register :
//!   bit 7: Negative flag
//!   bit 6: oVerflow flag
//!   bit 5: not used             (open circuit, always 1)
//!   bit 4: Break interrupt mode (open circuit, always 1)
//!   bit 3: Decimal mode
//!   bit 2: Interrupt disable
//!   bit 1: Zero flag
//!   bit 0: Carry flag
//! command pointer: 16 bit address register
//! stack pointer: 8 bits at page 0x0100, set at 0xff at start.
//! The way the BREAK bit works is a bit puzzling but a quick read at
//! http://forum.6502.org/viewtopic.php?f=8&t=3111 explains this bit is only
//! aimed at being saved in the stack to determine if it is a hard or soft
//! interrupt in the interrupt service routine (see
//! http://6502.org/tutorials/interrupts.html).

use super::memory::MemoryStack as Memory;
use super::memory::{AddressableIO, MemoryError};
use std::fmt;
use rand::random;
pub const STACK_BASE_ADDR: usize = 0x0100;

pub struct Registers {
    pub accumulator: u8,
    pub register_x: u8,
    pub register_y: u8,
    status_register: u8,
    pub command_pointer: usize,
    pub stack_pointer: u8,
}

const N_SHIFT: u8 = 7;
const V_SHIFT: u8 = 6;
const D_SHIFT: u8 = 3;
const I_SHIFT: u8 = 2;
const Z_SHIFT: u8 = 1;
const C_SHIFT: u8 = 0;

macro_rules! flag_fns {
    ($get_name:ident, $set_name:ident, $shift:expr) => {
        pub fn $get_name(&self) -> bool {
            self.status_register & (1 << $shift) != 0
        }
        pub fn $set_name(&mut self, flag: bool) {
            self.status_register &= !(1 << $shift);
            self.status_register |= (flag as u8) << $shift;
        }
    };
}

impl Registers {
    pub fn new(init_address: usize) -> Registers {
        Registers {
            accumulator: random::<u8>(),
            register_x: random::<u8>(),
            register_y: random::<u8>(),
            status_register: (random::<u8>() | 0b00111100) & 0b11110111, // 0bXX1101XX
            command_pointer: init_address,
            stack_pointer: random::<u8>(),
        }
    }

    pub fn new_initialized(init_address: usize) -> Registers {
        let mut registers = Registers::new(0);
        registers.initialize(init_address);

        registers
    }

    pub fn initialize(&mut self, init_address: usize) {
        self.accumulator = 0x00;
        self.register_x =  0x00;
        self.register_y =  0x00;
        self.status_register =  0b00110000;
        self.command_pointer =  init_address;
        self.stack_pointer =  0xff;
    }

    pub fn get_status_register(&self) -> u8 {
        self.status_register | 0b0011_0000 // auto set bits 4 & 5.
    }

    pub fn set_status_register(&mut self, status: u8) {
        self.status_register = status;
    }

    pub fn stack_push(
        &mut self,
        memory: &mut Memory,
        byte: u8,
    ) -> std::result::Result<(), MemoryError> {
        memory.write(STACK_BASE_ADDR + self.stack_pointer as usize, &vec![byte])?;
        let (sp, _) = self.stack_pointer.overflowing_sub(1);
        self.stack_pointer = sp;

        Ok(())
    }

    pub fn stack_pull(&mut self, memory: &Memory) -> std::result::Result<u8, MemoryError> {
        let (sp, _) = self.stack_pointer.overflowing_add(1);
        self.stack_pointer = sp;
        memory.read_1(STACK_BASE_ADDR + self.stack_pointer as usize)
    }

    flag_fns!(n_flag_is_set, set_n_flag, N_SHIFT);
    flag_fns!(v_flag_is_set, set_v_flag, V_SHIFT);
    flag_fns!(d_flag_is_set, set_d_flag, D_SHIFT);
    flag_fns!(i_flag_is_set, set_i_flag, I_SHIFT);
    flag_fns!(z_flag_is_set, set_z_flag, Z_SHIFT);
    flag_fns!(c_flag_is_set, set_c_flag, C_SHIFT);

    pub fn format_status(&self) -> String {
        format!(
            "{}{}-B{}{}{}{}",
            if self.n_flag_is_set() { "N" } else { "n" },
            if self.v_flag_is_set() { "V" } else { "v" },
            if self.d_flag_is_set() { "D" } else { "d" },
            if self.i_flag_is_set() { "I" } else { "i" },
            if self.z_flag_is_set() { "Z" } else { "z" },
            if self.c_flag_is_set() { "C" } else { "c" },
        )
    }
}

impl fmt::Debug for Registers {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Registers [A:0x{:02x}, X:0x{:02x}, Y:0x{:02x} | SP:0x{:02x}, CP:0x{:04x} | {}]",
            self.accumulator,
            self.register_x,
            self.register_y,
            self.stack_pointer,
            self.command_pointer,
            self.format_status()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_flags() {
        let registers = Registers::new(0x1000);
        assert!(registers.i_flag_is_set());
        assert!(!registers.d_flag_is_set());
        assert_eq!(0x1000, registers.command_pointer);
    }

    #[test]
    fn test_init_flags() {
        let registers = Registers::new_initialized(0x1000);
        assert!(!registers.z_flag_is_set());
        assert!(!registers.n_flag_is_set());
        assert!(!registers.i_flag_is_set());
        assert!(!registers.d_flag_is_set());
        assert!(!registers.c_flag_is_set());
        assert!(!registers.v_flag_is_set());
        assert_eq!(0x1000, registers.command_pointer);
        assert_eq!(0, registers.accumulator);
        assert_eq!(0, registers.register_x);
        assert_eq!(0, registers.register_y);
        assert_eq!(0xff, registers.stack_pointer);
    }

    #[test]
    fn test_set_flags() {
        let mut registers = Registers::new(0x1000);
        registers.set_c_flag(true);
        registers.set_v_flag(true);
        registers.set_z_flag(true);
        registers.set_n_flag(true);
        assert!(registers.c_flag_is_set());
        assert!(registers.v_flag_is_set());
        assert!(registers.z_flag_is_set());
        assert!(registers.n_flag_is_set());
        registers.set_z_flag(false);
        registers.set_n_flag(false);
        registers.set_c_flag(false);
        registers.set_v_flag(false);
        assert!(!registers.z_flag_is_set());
        assert!(!registers.n_flag_is_set());
        assert!(!registers.c_flag_is_set());
        assert!(!registers.v_flag_is_set());
    }
}
