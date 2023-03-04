use super::memory;
use super::memory::MemoryStack as Memory;
use super::memory::{little_endian, AddressableIO, MemoryError};
use super::registers::Registers;
use std::error;
use std::fmt;

pub type Result<T> = std::result::Result<T, ResolutionError>;

#[derive(Debug, Eq, PartialEq, Copy, Clone, Hash)]
pub enum ResolutionError {
    Solving(AddressingMode, usize, Option<usize>),
    Memory(MemoryError),
}

impl fmt::Display for ResolutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            ResolutionError::Solving(addressing_mode, opcode_address, target_address) => {
                let dst_addr_message = match target_address {
                    Some(v) => format!("#0x{:04X}", v),
                    None => format!("none"),
                };

                write!(f, "resolution error for addressing mode '{}' for opcode at address #0x{:04X}, resolution result: {}", addressing_mode, opcode_address, dst_addr_message)
            }
            ResolutionError::Memory(e) => {
                write!(f, "memory error during addressing mode resolution: {}", e)
            }
        }
    }
}

impl error::Error for ResolutionError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl std::convert::From<memory::MemoryError> for ResolutionError {
    fn from(err: memory::MemoryError) -> ResolutionError {
        ResolutionError::Memory(err)
    }
}

#[derive(Debug)]
pub struct AddressingModeResolution {
    pub addressing_mode: AddressingMode,
    pub target_address: Option<usize>,
}

impl AddressingModeResolution {
    fn new(
        addressing_mode: AddressingMode,
        target_address: Option<usize>,
    ) -> Self {
        AddressingModeResolution {
            addressing_mode, target_address,
        }
    }

    pub fn operands(&self) -> &[u8] {
        self.addressing_mode.get_operands()
    }
}

impl fmt::Display for AddressingModeResolution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.target_address {
            Some(addr) => write!(
                f,
                "{: <9}(#0x{:04X})",
                format!("{}", self.addressing_mode),
                addr
            ),
            None => write!(f, "{: <9}         ", format!("{}", self.addressing_mode)),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Copy, Clone, Hash)]
pub enum AddressingMode {
    Implied,
    Accumulator,
    Immediate([u8; 1]),
    ZeroPage([u8; 1]),
    ZeroPageXIndexed([u8; 1]),
    ZeroPageYIndexed([u8; 1]),
    ZeroPageXIndexedIndirect([u8; 1]),
    ZeroPageIndirectYIndexed([u8; 1]),
    ZeroPageIndirect([u8; 1]),
    Absolute([u8; 2]),
    AbsoluteXIndexed([u8; 2]),
    AbsoluteXIndexedIndirect([u8; 2]),
    AbsoluteYIndexed([u8; 2]),
    Indirect([u8; 2]),
    Relative(usize, [u8; 1]),
    ZeroPageRelative(usize, [u8; 2]),
}

impl AddressingMode {
    fn to_resolution(&self, addr: usize) -> AddressingModeResolution {
        AddressingModeResolution { addressing_mode: *self, target_address: Some(addr) }
    }
    fn to_resolution_no_addr(&self) -> AddressingModeResolution {
        AddressingModeResolution { addressing_mode: *self, target_address: None }
    }

    /*
     * solve
     * Create a AddressingModeResolution using the memory and/or registers for
     * each AddressingMode.
     */
    pub fn solve(
        &self,
        opcode_address: usize,
        memory: &Memory,
        registers: &Registers,
    ) -> Result<AddressingModeResolution> {
        Ok(match *self {
            AddressingMode::Implied => {
                self.to_resolution_no_addr()
            }
            AddressingMode::Accumulator => {
                self.to_resolution_no_addr()
            }
            AddressingMode::Immediate(v) => self.to_resolution(opcode_address + 1 as usize),
            AddressingMode::ZeroPage(v) => self.to_resolution(v[0] as usize),
            AddressingMode::ZeroPageXIndexed(v) => self.to_resolution((v[0] as usize + registers.register_x as usize) % 0x100),
            AddressingMode::ZeroPageYIndexed(v) => self.to_resolution((v[0] as usize + registers.register_y as usize) % 0x100),
            AddressingMode::ZeroPageXIndexedIndirect(v) => {
                let dst_addr = memory.read_le_u16((v[0] as usize + registers.register_x as usize) % 0x100)? as usize;

                if dst_addr > memory::MEMMAX {
                    return Err(ResolutionError::Solving(
                        *self,
                        opcode_address,
                        Some(dst_addr),
                    ))
                } else {
                    self.to_resolution(dst_addr)
                }
            }
            AddressingMode::ZeroPageIndirectYIndexed(v) => {
                let dst_addr =
                    memory.read_le_u16(v[0] as usize)? as usize + registers.register_y as usize;

                if dst_addr > memory::MEMMAX {
                    return Err(ResolutionError::Solving(
                        *self,
                        opcode_address,
                        Some(dst_addr),
                    ))
                } else {
                    self.to_resolution(dst_addr)
                }
            }
            AddressingMode::ZeroPageIndirect(v) => {
                let dst_addr = memory.read_le_u16(v[0] as usize)? as usize;
                self.to_resolution(dst_addr)
            }
            AddressingMode::Absolute(v) => {
                let dest_addr = little_endian(vec![v[0], v[1]]);
                self.to_resolution(dest_addr)
            }
            AddressingMode::AbsoluteXIndexed(v) => {
                let dest_addr = u16::from_le_bytes(v) as usize + registers.register_x as usize;
                self.to_resolution(dest_addr)
            }
            AddressingMode::AbsoluteXIndexedIndirect(v) => {
                let tmp_addr = u16::from_le_bytes(v) as usize + registers.register_x as usize;
                let dest_addr = memory.read_le_u16(tmp_addr)? as usize;
                self.to_resolution(dest_addr)
            }
            AddressingMode::AbsoluteYIndexed(v) => {
                let dest_addr = u16::from_le_bytes(v) as usize + registers.register_y as usize;
                self.to_resolution(dest_addr)
            }
            AddressingMode::Indirect(v) => {
                let dst_addr = memory.read_le_u16(u16::from_le_bytes(v) as usize)? as usize;
                self.to_resolution(dst_addr)
            }
            AddressingMode::Relative(_addr, v) => {
                self.to_resolution_no_addr()
            },
            AddressingMode::ZeroPageRelative(_addr, v) => {
                let dst_addr = v[0] as usize;
                self.to_resolution(dst_addr)
            }
        })
    }

    const NO_OPERANDS: &[u8] = &[];
    pub fn get_operands(&self) -> &[u8] {
        match self {
            AddressingMode::Implied => Self::NO_OPERANDS,
            AddressingMode::Accumulator => Self::NO_OPERANDS,
            AddressingMode::Immediate(v) => v,
            AddressingMode::ZeroPage(v) => v,
            AddressingMode::ZeroPageXIndexed(v) => v,
            AddressingMode::ZeroPageYIndexed(v) => v,
            AddressingMode::ZeroPageXIndexedIndirect(v) => v,
            AddressingMode::ZeroPageIndirectYIndexed(v) => v,
            AddressingMode::ZeroPageIndirect(v) => v,
            AddressingMode::Absolute(v) => v,
            AddressingMode::AbsoluteXIndexed(v) => v,
            AddressingMode::AbsoluteXIndexedIndirect(v) => v,
            AddressingMode::AbsoluteYIndexed(v) => v,
            AddressingMode::Indirect(v) => v,
            AddressingMode::Relative(_addr, v) => v,
            AddressingMode::ZeroPageRelative(_addr, v) => v,
        }
    }
}

impl fmt::Display for AddressingMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            AddressingMode::Implied => write!(f, ""),
            AddressingMode::Accumulator => write!(f, "A"),
            AddressingMode::Immediate(v) => write!(f, "#${:02x}", v[0]),
            AddressingMode::ZeroPage(v) => write!(f, "${:02x}", v[0]),
            AddressingMode::Absolute(v) => write!(f, "${:02X}{:02X}", v[1], v[0]),
            AddressingMode::AbsoluteXIndexed(v) => write!(f, "${:02X}{:02X},X", v[1], v[0]),
            AddressingMode::AbsoluteXIndexedIndirect(v) => {
                write!(f, "(${:02X}{:02X},X)", v[1], v[0])
            }
            AddressingMode::AbsoluteYIndexed(v) => write!(f, "${:02X}{:02X},Y", v[1], v[0]),
            AddressingMode::Indirect(v) => write!(f, "(${:02X}{:02X})", v[1], v[0]),
            AddressingMode::ZeroPageXIndexed(v) => write!(f, "${:02x},X", v[0]),
            AddressingMode::ZeroPageYIndexed(v) => write!(f, "${:02x},Y", v[0]),
            AddressingMode::ZeroPageXIndexedIndirect(v) => write!(f, "(${:02x},X)", v[0]),
            AddressingMode::ZeroPageIndirectYIndexed(v) => write!(f, "(${:02x}),Y", v[0]),
            AddressingMode::ZeroPageIndirect(v) => write!(f, "(${:02x})", v[0]),
            AddressingMode::Relative(addr, v) => {
                write!(f, "${:04X}", resolve_relative(addr, v[0]).unwrap())
            },
            AddressingMode::ZeroPageRelative(addr, v) => {
                write!(f, "${:02x},${:04X}", v[0], resolve_relative(addr, v[1]).unwrap())
            },
        }
    }
}

pub fn resolve_relative(addr: usize, offset: u8) -> Option<usize> {
    let offset_i8 = i8::from_le_bytes(offset.to_le_bytes());
    if offset_i8 < 0 {
        addr.checked_sub((-2 - offset_i8) as usize)
    } else {
        addr.checked_add((offset_i8 as usize) + 2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_implied() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xe8, 0xff, 0xff]).unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::Implied;
        assert_eq!("".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(0, resolution.operands().len());
        assert_eq!(None, resolution.target_address);
        assert_eq!("", format!("{}", resolution).as_str().trim());
    }

    #[test]
    fn test_accumulator() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xe8, 0xff, 0xff]).unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::Accumulator;
        assert_eq!("A".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(0, resolution.operands().len());
        assert_eq!(None, resolution.target_address);
        assert_eq!("A", format!("{}", resolution).as_str().trim());
    }

    #[test]
    fn test_immediate() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xe8, 0xff, 0xff]).unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::Immediate([0xff]);
        assert_eq!("#$ff".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0xff], resolution.operands());
        assert_eq!(0x1001, resolution.target_address.unwrap());
        assert_eq!("#$ff     (#0x1001)".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_zero_page() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xa5, 0x21, 0x22]).unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::ZeroPage([0x21]);
        assert_eq!("$21".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x21], resolution.operands());
        assert_eq!(0x0021, resolution.target_address.unwrap());
        assert_eq!("$21      (#0x0021)".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_absolute() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xa5, 0x21, 0x2a]).unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::Absolute([0x21, 0x2a]);
        assert_eq!("$2A21".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x21, 0x2a], resolution.operands());
        assert_eq!(0x2a21, resolution.target_address.unwrap());
        assert_eq!("$2A21    (#0x2A21)".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_absolute_x_indexed() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xa5, 0x21, 0x22]).unwrap();
        let mut registers = Registers::new(0x1000);
        registers.register_x = 0x05;
        let am = AddressingMode::AbsoluteXIndexed([0x21, 0x22]);
        assert_eq!("$2221,X".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x21, 0x22], resolution.operands());
        assert_eq!(0x2226, resolution.target_address.unwrap());
        assert_eq!("$2221,X  (#0x2226)".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_absolute_y_indexed() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xa5, 0x21, 0x22]).unwrap();
        let mut registers = Registers::new(0x1000);
        registers.register_y = 0x16;
        let am = AddressingMode::AbsoluteYIndexed([0x21, 0x22]);
        assert_eq!("$2221,Y".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x21, 0x22], resolution.operands());
        assert_eq!(0x2237, resolution.target_address.unwrap());
        assert_eq!("$2221,Y  (#0x2237)".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_indirect() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xa5, 0x21, 0x22]).unwrap();
        memory.write(0x2221, &vec![0x0a, 0x80]).unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::Indirect([0x21, 0x22]);
        assert_eq!("($2221)".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x21, 0x22], resolution.operands());
        assert_eq!(0x800a, resolution.target_address.unwrap());
        assert_eq!("($2221)  (#0x800A)".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_zero_page_x_indexed() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xa5, 0x21, 0x22]).unwrap();
        let mut registers = Registers::new(0x1000);
        registers.register_x = 0x05;
        let am = AddressingMode::ZeroPageXIndexed([0x21]);
        assert_eq!("$21,X".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x21], resolution.operands());
        assert_eq!(0x0026, resolution.target_address.unwrap());
        assert_eq!("$21,X    (#0x0026)".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_zero_page_y_indexed() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xa5, 0x21, 0x22]).unwrap();
        let mut registers = Registers::new(0x1000);
        registers.register_y = 0x05;
        let am = AddressingMode::ZeroPageYIndexed([0x21]);
        assert_eq!("$21,Y".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x21], resolution.operands());
        assert_eq!(0x0026, resolution.target_address.unwrap());
        assert_eq!("$21,Y    (#0x0026)".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_zero_page_wraparound() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xa5, 0x21, 0x22]).unwrap();
        let mut registers = Registers::new(0x1000);
        registers.register_y = 0x15;
        let am = AddressingMode::ZeroPageYIndexed([0xeb]);
        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(0x0000, resolution.target_address.unwrap());
    }

    #[test]
    fn test_zero_page_indirect_y_indexed() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xa5, 0x21, 0x22]).unwrap();
        memory.write(0x0021, &vec![0x05, 0x80]).unwrap();
        let mut registers = Registers::new(0x1000);
        registers.register_y = 0x05;
        let am = AddressingMode::ZeroPageIndirectYIndexed([0x21]);
        assert_eq!("($21),Y".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x21], resolution.operands());
        assert_eq!(0x800a, resolution.target_address.unwrap());
        assert_eq!("($21),Y  (#0x800A)".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_relative_positive() {
        let mut memory = Memory::new_with_ram();
        memory
            .write(0x1000, &vec![0xd0, 0x04, 0x22, 0x00, 0x12, 0x0a])
            .unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::Relative(0x1000, [0x04]);
        assert_eq!("$1006".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x04], resolution.operands());
        assert_eq!(None, resolution.target_address);
        assert_eq!("$1006             ".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_relative_negative() {
        let mut memory = Memory::new_with_ram();
        memory
            .write(
                0x0ffa,
                &vec![
                    0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff, 0xd0, 0xfb, 0x22, 0x00, 0x12, 0x0a,
                ],
            )
            .unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::Relative(0x1000, [0xfb]);
        assert_eq!("$0FFD".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0xfb], resolution.operands());
        assert_eq!(None, resolution.target_address);
        assert_eq!("$0FFD             ".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_relative_negative_edge() {
        let mut memory = Memory::new_with_ram();
        memory
            .write(
                0x0ffa,
                &vec![
                    0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff, 0xd0, 0x80, 0x22, 0x00, 0x12, 0x0a,
                ],
            )
            .unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::Relative(0x1000, [0x80]);
        assert_eq!("$0F82".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x80], resolution.operands());
        assert_eq!(None, resolution.target_address);
        assert_eq!("$0F82             ".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_relative_positive_edge() {
        let mut memory = Memory::new_with_ram();
        memory
            .write(
                0x0ffa,
                &vec![
                    0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff, 0xd0, 0x7f, 0x22, 0x00, 0x12, 0x0a,
                ],
            )
            .unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::Relative(0x1000, [0x7f]);
        assert_eq!("$1081".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x7f], resolution.operands());
        assert_eq!(None, resolution.target_address);
        assert_eq!("$1081             ".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_zero_page_indirect() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xa5, 0x21, 0x22]).unwrap();
        memory.write(0x0021, &vec![0x05, 0x80]).unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::ZeroPageIndirect([0x21]);
        assert_eq!("($21)".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x21], resolution.operands());
        assert_eq!(0x8005, resolution.target_address.unwrap());
        assert_eq!("($21)    (#0x8005)".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_absolute_x_indexed_indirect() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xa5, 0x21, 0x20]).unwrap();
        memory.write(0x2025, &vec![0x05, 0x80]).unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::AbsoluteXIndexedIndirect([0x21, 0x20]);
        assert_eq!("($2021,X)".to_owned(), format!("{}", am));

        registers.register_x = 0x04;
        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x21, 0x20], resolution.operands());
        assert_eq!(0x8005, resolution.target_address.unwrap());
        assert_eq!("($2021,X)(#0x8005)".to_owned(), format!("{}", resolution));
    }

    #[test]
    fn test_zero_page_relative() {
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &vec![0xa5, 0x25, 0x20]).unwrap();
        memory.write(0x0025, &vec![0x05, 0x80]).unwrap();
        let mut registers = Registers::new(0x1000);
        let am = AddressingMode::ZeroPageRelative(0x1000, [0x25, 0x20]);
        assert_eq!("$25,$1022".to_owned(), format!("{}", am));

        let resolution: AddressingModeResolution =
            am.solve(0x1000, &mut memory, &mut registers).unwrap();
        assert_eq!(vec![0x25, 0x20], resolution.operands());
        assert_eq!(0x0025, resolution.target_address.unwrap());
        assert_eq!("$25,$1022(#0x0025)".to_owned(), format!("{}", resolution));
    }
}
