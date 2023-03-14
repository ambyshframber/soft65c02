//! A bug-accurate emulation of the W65C51N ACIA, a serial interface chip designed to support the 65C02.
//! 
//! The emulated chip gets input from a separate file, NOT the process' stdin. This is because stdin is used for the control repl. Because of this, the emulation only works on Unix-like systems because it needs the read call to return instantly if the input file or pipe is empty. You might be able to make it work on Windows, but I don't even know what to google to figure that out. Good luck!
//! 
//! The output can be anything that is Write.

use std::io::{BufReader, Read, BufWriter, Write, Result};
use std::path::Path;
use libc::O_NDELAY;
use std::fs::{OpenOptions, File};
use std::os::unix::fs::OpenOptionsExt;
use std::cell::RefCell;
use super::*;

struct W65C51N<R: Read, W: Write> {
    src: BufReader<R>,
    dst: BufWriter<W>,

    rxdr: u8,
    rxdr_dirty: RefCell<bool>,
}

impl<R: Read, W: Write> W65C51N<R, W> {
    fn init(src: R, dst: W) -> W65C51N<R, W> {
        let src = BufReader::new(src);
        let dst = BufWriter::new(dst);
        W65C51N {
            src, dst,
            rxdr: 0,
            rxdr_dirty: RefCell::new(false)
        }
    }
}
impl<R: Read, W: Write> AddressableIO for W65C51N<R, W> {
    fn update(&mut self) -> bool {
        let dirty = self.rxdr_dirty.get_mut();
        if !*dirty {
            let mut b = [0u8];
            if let Ok(1) = self.src.read(&mut b) {
                self.rxdr = b[0]
            }
            *dirty = true
        }

        false
    }

    fn read_1(&self, addr: usize) -> MemResult<u8> {
        match addr {
            0 => { // read rx
                let mut dirty = self.rxdr_dirty.borrow_mut();
                *dirty = false;
                Ok(self.rxdr)
            }
            _ => Ok(0) // for now
        }
    }

    fn write(&mut self, location: usize, data: &[u8]) -> MemResult<()> {
        

        Ok(())
    }

    fn get_size(&self) -> usize {
        4
    }
}

impl<W: Write> W65C51N<File, W> {
    /// Create a W65C51N that outputs to `dst`.
    /// 
    /// Opening the input file/pipe is handled in here because it needs specific flags.
    pub fn new<P: AsRef<Path>>(src: P, dst: W) -> Result<W65C51N<File, W>> {
        let src = OpenOptions::new().custom_flags(O_NDELAY).read(true).open(src)?;
        Ok(W65C51N::init(src, dst))
    }
}
