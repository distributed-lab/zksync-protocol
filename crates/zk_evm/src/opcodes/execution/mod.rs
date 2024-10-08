use super::*;
use crate::vm_state::*;
use crate::zkevm_opcode_defs::decoding::AllowedPcOrImm;
use crate::zkevm_opcode_defs::decoding::VmEncodingMode;

pub mod add;
pub mod binop;
pub mod context;
pub mod div;
pub mod far_call;
pub mod jump;
pub mod log;
pub mod mul;
pub mod near_call;
pub mod noop;
pub mod ptr;
pub mod ret;
pub mod shift;
pub mod sub;
pub mod uma;
