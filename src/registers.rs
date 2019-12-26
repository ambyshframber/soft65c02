use std::fmt;

/*
 * 65C02 registers
 * accumulator, X & Y registers are 8 bits general purpose registers.
 * status flags register :
 * bit 8: Negative flag
 * bit 7: oVerflow flag
 * bit 6: not used
 * bit 5: Break interrupt mode
 * bit 4: Decimal mode
 * bit 3: Interrupt disable
 * bit 2: Zero flag
 * bit 1: Carry flag
 *
 * command pointer: 16 bit address register
 * stack pointer: 8 bits at page 0x0100, set at 0xff at start.
 */
pub struct Registers {
    pub accumulator:        u8,
    pub register_x:         u8,
    pub register_y:         u8,
    pub status_register:    u8,
    pub command_pointer:    usize,
    pub stack_pointer:      u8,
}

impl Registers {
    pub fn new(init_address: usize) -> Registers {
        Registers {
            accumulator:        0x00,
            register_x:         0x00,
            register_y:         0x00,
            status_register:    0b00110000,
            command_pointer:    init_address,
            stack_pointer:      0xff,
        }
    }
}

impl Registers {
    pub fn n_flag_is_set(&self) -> bool {
        self.status_register & 0b10000000 == 0b10000000
    }

    pub fn v_flag_is_set(&self) -> bool {
        self.status_register & 0b01000000 == 0b01000000
    }

    pub fn b_flag_is_set(&self) -> bool {
        self.status_register & 0b00010000 == 0b00010000
    }

    pub fn d_flag_is_set(&self) -> bool {
        self.status_register & 0b00001000 == 0b00001000
    }

    pub fn i_flag_is_set(&self) -> bool {
        self.status_register & 0b00000100 == 0b00000100
    }

    pub fn z_flag_is_set(&self) -> bool {
        self.status_register & 0b00000010 == 0b00000010
    }

    pub fn c_flag_is_set(&self) -> bool {
        self.status_register & 0b00000001 == 0b00000001
    }

    pub fn set_n_flag(&mut self, flag: bool) {
        if flag {
            self.status_register |= 0b10000000;
        } else {
            self.status_register &= 0b01111111;
        }
    }

    pub fn set_v_flag(&mut self, flag: bool) {
        if flag {
            self.status_register |= 0b01000000;
        } else {
            self.status_register &= 0b10111111;
        }
    }

    pub fn set_b_flag(&mut self, flag: bool) {
        if flag {
            self.status_register |= 0b00010000;
        } else {
            self.status_register &= 0b11101111;
        }
    }

    pub fn set_d_flag(&mut self, flag: bool) {
        if flag {
            self.status_register |= 0b00001000;
        } else {
            self.status_register &= 0b11110111;
        }
    }

    pub fn set_i_flag(&mut self, flag: bool) {
        if flag {
            self.status_register |= 0b00000100;
        } else {
            self.status_register &= 0b11111011;
        }
    }

    pub fn set_z_flag(&mut self, flag: bool) {
        if flag {
            self.status_register |= 0b00000010;
        } else {
            self.status_register &= 0b11111101;
        }
    }

    pub fn set_c_flag(&mut self, flag: bool) {
        if flag {
            self.status_register |= 0b00000001;
        } else {
            self.status_register &= 0b11111110;
        }
    }
}

impl fmt::Debug for Registers {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
        f,
        "Registers {{ A: {:02x}, X: {:02x}, Y: {:02x} | SP: {:02x} CP: {:04x}\rNV-BDIZC\r{:08b} }}",
        self.accumulator,
        self.register_x,
        self.register_y,
        self.stack_pointer,
        self.command_pointer,
        self.status_register
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init_flags() {
        let mut registers = Registers::new(0x1000);
        assert!(!registers.z_flag_is_set());
        assert!(!registers.n_flag_is_set());
        assert!(registers.b_flag_is_set());
        assert!(!registers.i_flag_is_set());
        assert!(!registers.d_flag_is_set());
        assert!(!registers.c_flag_is_set());
        assert!(!registers.v_flag_is_set());
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
