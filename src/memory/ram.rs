use super::*;

/// Basic RAM.
pub struct RAM {
    ram: Vec<u8>,
}

impl RAM {
    pub fn new() -> RAM {
        RAM {
            ram: vec![0; 65536]
        }
    }

    pub fn new_with_size(len: usize) -> RAM {
        RAM { ram: vec![0; len] }
    }
}

impl AddressableIO for RAM {
    fn read_1(&self, addr: usize) -> MemResult<u8> {
        self.ram.get(addr).copied().ok_or(MemoryError::ReadOverflow(1, addr))
    }

    fn read_n(&self, addr: usize, len: usize) -> Result<Vec<u8>, MemoryError> {
        if self.ram.len() >= addr + len {
            Ok(self.ram[addr..addr + len].to_vec())
        } else {
            Err(MemoryError::ReadOverflow(len, addr))
        }
    }

    fn write(&mut self, location: usize, data: &[u8]) -> Result<(), MemoryError> {
        if location + data.len() > self.ram.len() {
            Err(MemoryError::WriteOverflow(
                data.len(), location
            ))
        } else {
            for offset in 0..data.len() {
                self.ram[usize::from(location) + offset] = data[offset];
            }

            Ok(())
        }
    }

    fn get_size(&self) -> usize {
        self.ram.len()
    }
}

impl DebugIO for RAM {}
