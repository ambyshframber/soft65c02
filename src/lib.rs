mod memory;
mod registers;
mod addressing_mode;
mod cpu_instruction;
mod processing_unit;

use memory::RAM as Memory;
use registers::Registers;
use processing_unit::*;

fn mem_dump(start: usize, end: usize, memory: &Memory) {
    let mut line = String::new();
    let address = start;
    let bytes = memory.read(start, end - start + 1).unwrap();

    while address < end {
        if address % 16 == start % 16 {
            println!("{}", line);
            line = format!("#{:04X}: ", address);
        } else if address % 8 == start % 8 {
            line = format!("{} ", line);
        }

        line = format!("{} {:02x}", line, bytes[address]);
    }

    println!("{}", line);
}



#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let init_vector:usize = 0x0800;
        let mut memory = memory::RAM::new();
        memory.write(init_vector, vec![0x48, 0xa9, 0x01, 0x8d, 0x00, 0x02, 0x6c, 0x00, 0x02, 0x95, 0x20, 0xa1, 0x20, 0x51, 0x21, 0x96, 0x21, 0x7d, 0x01, 0x02, 0xf9, 0x10, 0x12, 0xd0, 0xf6]).unwrap();
        let expected_output:Vec<&str> = vec![
        "#0x0800: (48)          PHA",
        "#0x0801: (a9 01)       LDA  #$01",
        "#0x0803: (8d 00 02)    STA  $0200",
        "#0x0806: (6c 00 02)    JMP  ($0200)",
        "#0x0809: (95 20)       STA  $20,X",
        "#0x080B: (a1 20)       LDA  ($20,X)",
        "#0x080D: (51 21)       EOR  ($21),Y",
        "#0x080F: (96 21)       STX  $21,Y",
        "#0x0811: (7d 01 02)    ADC  $0201,X",
        "#0x0814: (f9 10 12)    SBC  $1210,Y",
        "#0x0817: (d0 f6)       BNE  -10",
        "#0x0819: (00)          BRK"
        ];
        let registers = Registers::new(init_vector);
        let mut count:usize = 0;
        let output = disassemble(init_vector, 0x0819, &registers, &memory);

        for line in output {
            assert_eq!(format!("{}", expected_output[count]), format!("{}", line).as_str().trim().to_owned());
            count = count + 1;
        }
    }
}
