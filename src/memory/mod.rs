mod error;
mod ram;
pub use error::MemoryError;
pub use ram::RAM;

pub const MEMMAX:usize = 65535;

pub fn little_endian(bytes: Vec<u8>) -> usize {
    let mut addr:usize = 0;

    for byte in bytes.iter().rev() {
        addr = addr << 8 | (*byte as usize);
    }

    addr
}

/*
 * AddressableIO
 * this trait defines the interface for all memory systems
 */
pub trait AddressableIO {
    fn read(&self, addr: usize, len: usize) -> Result<Vec<u8>, MemoryError>;
    fn write(&mut self, location: usize, data: Vec<u8>) -> Result<(), MemoryError>;
    fn get_size(&self) -> usize;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_little_endian() {
        assert_eq!(0x1234, little_endian(vec![0x34, 0x12]));
        assert_eq!(0x0011, little_endian(vec![0x11, 0x00]));
        assert_eq!(0x1100, little_endian(vec![0x00, 0x11]));
    }
}
