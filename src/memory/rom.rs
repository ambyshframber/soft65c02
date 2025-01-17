use super::*;

/// Read-only memory.
pub struct ROM {
    rom: Vec<u8>,
}

impl ROM {
    pub fn new(data: Vec<u8>) -> ROM {
        ROM {
            rom: data,
        }
    }
}

impl AddressableIO for ROM {
    fn read_1(&self, addr: usize) -> MemResult<u8> {
        self.rom.get(addr).copied().ok_or(MemoryError::ReadOverflow(1, addr))
    }
    fn read_n(&self, addr: usize, len: usize) -> Result<Vec<u8>, MemoryError> {
        if self.rom.len() >= addr + len {
            Ok(self.rom[addr..addr + len].to_vec())
        } else {
            Err(MemoryError::ReadOverflow(len, addr))
        }
    }

    fn write(&mut self, location: usize, _data: &[u8]) -> Result<(), MemoryError> {
        Err(MemoryError::Other(
            location,
            "trying to write in a read-only memory",
        ))
    }

    fn get_size(&self) -> usize {
        self.rom.len()
    }
}

impl DebugIO for ROM {}
