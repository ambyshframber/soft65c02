use minifb::{Key, Window, WindowOptions, Error, ScaleMode, Scale};
use soft65c02::{Memory, Registers, AddressableIO, LogLine};
use soft65c02::memory::{MINIFB_HEIGHT, MINIFB_WIDTH, MiniFBMemoryAdapter};
use std::io;
use std::io::prelude::*;
use std::fs::File;
use std::{thread, time};

fn init_window() -> Window {
    let mut window = Window::new(
            "65C02 computer graphic example",
            MINIFB_WIDTH,
            MINIFB_HEIGHT,
            WindowOptions {
            resize: true,
            scale: Scale::X4,
            scale_mode: ScaleMode::AspectRatioStretch,
            ..WindowOptions::default()
        },
    )
    .expect("Failed to open window.");

    // Limit to max ~60 fps update rate
    window.limit_update_rate(Some(std::time::Duration::from_micros(16600)));

    window
}


fn main(){
    let init_vector:usize = 0x1B00;
    let mut memory = Memory::new_with_ram();
    {
        let mut f = File::open("point.bin").unwrap();
        let mut buffer:Vec<u8> = vec![];
        f.read_to_end(&mut buffer).unwrap();
        let len = buffer.len();
        memory.write(init_vector, buffer).unwrap();
        for line in soft65c02::disassemble(init_vector, init_vector + len, &memory).iter() {
            println!("{}", line);
        }
    }
    let mut window = init_window();
    memory.add_subsystem("VIDEO TERMINAL", 0x0200, MiniFBMemoryAdapter::new(window));
    let mut registers = Registers::new(init_vector);
    let mut cp = 0x0000;
    let mut f = File::create("log.txt").unwrap();

    while cp != registers.command_pointer {
        cp = registers.command_pointer;
        writeln!(f, "{}", soft65c02::execute_step(&mut registers, &mut memory).unwrap());
        thread::sleep(time::Duration::from_millis(1));
    }
}
