use soft65c02::{AddressableIO, Memory, MemoryParserIterator};
use std::fs::File;
use std::io::prelude::*;
use structopt::StructOpt;

#[derive(StructOpt, Debug)]
#[structopt(name = "disassembler")]
struct CLOptions {
    // binary file to read
    #[structopt(short, long)]
    filename: String,

    // address to start reading
    #[structopt(short, long, default_value = "0")]
    start_address: String,

    // number of commands to read
    #[structopt(short, long, default_value = "0")]
    commands: usize,
}

impl CLOptions {
    pub fn get_start_address(&self) -> usize {
        usize::from_str_radix(&self.start_address, 16).unwrap() & 0xffff
    }
}

fn read_file(filename: &str) -> Vec<u8> {
    let mut f = File::open(filename).unwrap();
    let mut buffer: Vec<u8> = vec![];
    f.read_to_end(&mut buffer).unwrap();
    buffer
}

fn main() {
    let cli_opt = CLOptions::from_args();
    let bytes = read_file(cli_opt.filename.as_str());
    let mut memory = Memory::new_with_ram();
    memory.write(0x0000, &bytes).unwrap();

    for (op, line) in MemoryParserIterator::new(cli_opt.get_start_address(), &memory).enumerate() {
        println!("{}", line);
        if cli_opt.commands != 0 && (op >= cli_opt.commands) {
            break;
        }
    }
}
