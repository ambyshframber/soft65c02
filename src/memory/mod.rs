//! Memory operations and interfaces.

use std::fmt;

mod error;
mod memory_stack;
mod minifb_sub;
mod ram;
mod rom;
#[cfg(unix)]
mod w65c51n;

pub use error::*;
pub use memory_stack::MemoryStack;
pub use minifb_sub::MiniFBMemory;
pub use ram::RAM;
pub use rom::ROM;

pub const MEMMAX: usize = 65535;

/// This trait defines the interface for all memory systems
pub trait AddressableIO {
    fn read_1(&self, addr: usize) -> MemResult<u8>;
    fn read_2(&self, addr: usize) -> MemResult<[u8; 2]> {
        let lo = self.read_1(addr)?;
        let hi = self.read_1(addr + 1)?;
        Ok([lo, hi])
    }
    fn read_le_u16(&self, addr: usize) -> MemResult<u16> {
        Ok(u16::from_le_bytes(self.read_2(addr)?))
    }
    fn read_n(&self, addr: usize, len: usize) -> MemResult<Vec<u8>> {
        (addr..addr + len).map(|addr| self.read_1(addr)).collect()
    }

    fn write(&mut self, location: usize, data: &[u8]) -> MemResult<()>;
    
    fn get_size(&self) -> usize;
    /// returns `true` if the device is asserting an interrupt
    fn update(&mut self) -> bool { false }
}

/*
 * TODO: this is completely broken.
 */
pub trait DebugIO: AddressableIO {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut line = String::new();
        let size = self.get_size();
        let bytes = self.read_n(0, size).unwrap();

        for address in 0..size { // format as hexdump
            if address % 16 == 0 {
                write!(f, "{}", line).unwrap();
                line = format!("#{:04X}: ", address);
            } else if address % 8 == 0 {
                line = format!("{} ", line);
            }

            line = format!("{} {:02x}", line, bytes[address]);
        }

        write!(f, "{}", line)
    }
}

