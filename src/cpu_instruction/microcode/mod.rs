mod error;
pub use error::{MicrocodeError, Result};

pub use crate::cpu_instruction::{CPUInstruction, LogLine};
pub use crate::registers::{Registers, STACK_BASE_ADDR};
pub use crate::memory::MemoryStack as Memory;
pub use crate::memory::{AddressableIO, little_endian, MemoryError};
pub use crate::addressing_mode::*;
pub use super::{INTERRUPT_VECTOR_ADDR, INIT_VECTOR_ADDR};

mod adc;
mod and;
mod asl;
mod bcc;
mod bcs;
mod beq;
mod bit;
mod bmi;
mod bne;
mod bpl;
mod bra;
mod brk;
mod bvc;
mod bvs;
mod clc;
mod cld;
mod cli;
mod clv;
mod cmp;
mod cpx;
mod cpy;
mod dec;
mod dex;
mod dey;
mod eor;
mod inc;
mod inx;
mod iny;
mod jmp;
mod jsr;
mod lda;
mod ldx;
mod ldy;
mod lsr;
mod nop;
mod ora;
mod pha;
mod php;
mod phx;
mod phy;
mod pla;
mod plp;
mod plx;
mod ply;
mod rol;
mod ror;
mod rti;
mod rts;
mod sbc;
mod sta;
mod stp;
mod stx;
mod stz;
mod tax;

pub use adc::adc;
pub use and::and;
pub use asl::asl;
pub use bcc::bcc;
pub use bcs::bcs;
pub use beq::beq;
pub use bit::bit;
pub use bmi::bmi;
pub use bne::bne;
pub use bpl::bpl;
pub use bra::bra;
pub use brk::brk;
pub use bvc::bvc;
pub use bvs::bvs;
pub use clc::clc;
pub use cld::cld;
pub use cli::cli;
pub use clv::clv;
pub use cmp::cmp;
pub use cpx::cpx;
pub use cpy::cpy;
pub use dec::dec;
pub use dex::dex;
pub use dey::dey;
pub use eor::eor;
pub use inc::inc;
pub use inx::inx;
pub use iny::iny;
pub use jmp::jmp;
pub use jsr::jsr;
pub use lda::lda;
pub use ldx::ldx;
pub use ldy::ldy;
pub use lsr::lsr;
pub use nop::nop;
pub use ora::ora;
pub use pha::pha;
pub use php::php;
pub use phx::phx;
pub use phy::phy;
pub use pla::pla;
pub use plp::plp;
pub use plx::plx;
pub use ply::ply;
pub use rol::rol;
pub use ror::ror;
pub use rti::rti;
pub use rts::rts;
pub use sbc::sbc;
pub use sta::sta;
pub use stp::stp;
pub use stx::stx;
pub use stz::stz;
pub use tax::tax;
