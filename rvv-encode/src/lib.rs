#[macro_use]
extern crate pest_derive;

use anyhow::{anyhow, Error};
use pest::Parser;

#[allow(dead_code, clippy::type_complexity)]
mod opcodes;

mod asm_parser {
    #[derive(Parser)]
    #[grammar = "asm.pest"]
    pub(crate) struct AsmParser;
}
use asm_parser::{AsmParser, Rule};

// The last register must be `v0`
const V0_TAIL_INSTS: [&str; 14] = [
    "vfmerge.vfm",
    "vadc.vxm",
    "vmadc.vxm",
    "vsbc.vxm",
    "vmsbc.vxm",
    "vmerge.vxm",
    "vadc.vvm",
    "vmadc.vvm",
    "vsbc.vvm",
    "vmsbc.vvm",
    "vmerge.vvm",
    "vadc.vim",
    "vmadc.vim",
    "vmerge.vim",
];

// https://github.com/riscv/riscv-v-spec/blob/master/v-spec.adoc#101-vector-arithmetic-instruction-encoding
//
// NOTE: For ternary multiply-add operations, the assembler syntax always places the
// destination vector register first, followed by either rs1 or vs1, then vs2.
// This ordering provides a more natural reading of the assembler for these
// ternary operations, as the multiply operands are always next to each other.
const VV_TERNARY_INSTS: [&str; 19] = [
    "vmacc.vv",
    "vnmsac.vv",
    "vmadd.vv",
    "vnmsub.vv",
    "vwmaccu.vv",
    "vwmacc.vv",
    "vwmaccsu.vv",
    "vfmacc.vv",
    "vfnmacc.vv",
    "vfmsac.vv",
    "vfnmsac.vv",
    "vfmadd.vv",
    "vfnmadd.vv",
    "vfmsub.vv",
    "vfnmsub.vv",
    "vfwmacc.vv",
    "vfwnmacc.vv",
    "vfwmsac.vv",
    "vfwnmsac.vv",
];
const VX_VF_TERNARY_INSTS: [&str; 20] = [
    "vmacc.vx",
    "vnmsac.vx",
    "vmadd.vx",
    "vnmsub.vx",
    "vwmaccu.vx",
    "vwmacc.vx",
    "vwmaccsu.vx",
    "vwmaccus.vx",
    "vfmacc.vf",
    "vfnmacc.vf",
    "vfmsac.vf",
    "vfnmsac.vf",
    "vfmadd.vf",
    "vfnmadd.vf",
    "vfmsub.vf",
    "vfnmsub.vf",
    "vfwmacc.vf",
    "vfwnmacc.vf",
    "vfwmsac.vf",
    "vfwnmsac.vf",
];

/// Convert one RISC-V Vector Extension(RVV) instruction into code.
///
/// This function try to parse the instruction as normal asm instruction or
/// standalone label ("1:"/"label:"). If it's a valid RVV instruction, it will
/// try to encode it to target code. Otherwise, if it's a valid asm instruction
/// it will return `Ok(None)`. If parse or encode failed, it will return error.
///
/// ## Example:
/// ```
/// assert_eq!(rvv_encode::encode("vle64.v v3, (a0), v0.t", false).unwrap(), Some(0b00000000000001010111000110000111));
/// ```
pub fn encode(inst: &str, reserved_only: bool) -> Result<Option<u32>, Error> {
    let pairs = if let Ok(result) = AsmParser::parse(Rule::inst, inst.trim()) {
        result
    } else {
        let _ = AsmParser::parse(Rule::label, inst.trim())
            .map_err(|err| anyhow!("parse asm error: {}", err))?;
        return Ok(None);
    };
    let mut name = "unknown";
    let mut args = Vec::new();
    for pair in pairs.clone() {
        for inner1_pair in pair.into_inner() {
            match inner1_pair.as_rule() {
                Rule::inst_name => {
                    name = inner1_pair.as_str();
                }
                Rule::inst_arg => {
                    for inner2_pair in inner1_pair.into_inner() {
                        match inner2_pair.as_rule() {
                            Rule::inst_arg_mask | Rule::inst_arg_simple | Rule::integer => {
                                args.push(inner2_pair.as_str());
                            }
                            _ => {
                                return Ok(None);
                            }
                        }
                    }
                }
                _ => {
                    return Ok(None);
                }
            }
        }
    }
    if reserved_only {
        let mut is_reserved = false;
        'outer: for width in [128, 256, 512, 1024] {
            for prefix in ["i", "e"] {
                let part = format!("{}{}", prefix, width);
                if name.contains(part.as_str()) {
                    is_reserved = true;
                    break 'outer;
                }
                for arg in &args {
                    if arg.contains(part.as_str()) {
                        is_reserved = true;
                        break 'outer;
                    }
                }
            }
        }
        if !is_reserved {
            return Ok(None);
        }
    }

    opcodes::INSTRUCTIONS
        .iter()
        .find(|(inst_name, _, _)| *inst_name == name)
        .map(|(_, base, args_cfg)| gen_inst_code(name, &args, *base, args_cfg))
        .transpose()
}

fn gen_inst_code(
    name: &str,
    args: &[&str],
    mut base: u32,
    arg_cfg: &[(&str, usize)],
) -> Result<u32, Error> {
    // The order of `simm5`/`vs1` and `vs2` in opcodes-rvv is not the same with v-spec.adoc
    let simm5_idx = arg_cfg.iter().position(|(name, _)| *name == "simm5");
    let vs1_idx = arg_cfg.iter().position(|(name, _)| *name == "vs1");
    let rs1_idx = arg_cfg.iter().position(|(name, _)| *name == "rs1");
    let vs2_idx = arg_cfg.iter().position(|(name, _)| *name == "vs2");
    let last_7bits = base & 0b1111111;
    let mut arg_cfg_vec = arg_cfg.iter().collect::<Vec<_>>();
    if let (Some(simm5_idx), Some(vs2_idx), 0x57) = (simm5_idx, vs2_idx, last_7bits) {
        arg_cfg_vec.swap(simm5_idx, vs2_idx);
    }
    if let (Some(vs1_idx), Some(vs2_idx), 0x57) = (vs1_idx, vs2_idx, last_7bits) {
        if !VV_TERNARY_INSTS.contains(&name) {
            arg_cfg_vec.swap(vs1_idx, vs2_idx);
        }
    }
    if let (Some(rs1_idx), Some(vs2_idx), 0x57) = (rs1_idx, vs2_idx, last_7bits) {
        if !VX_VF_TERNARY_INSTS.contains(&name) {
            arg_cfg_vec.swap(rs1_idx, vs2_idx);
        }
    }
    let arg_cfg_final = &arg_cfg_vec;

    let has_vm = arg_cfg_final.iter().any(|(arg_name, _)| *arg_name == "vm");
    let has_nf = arg_cfg_final.iter().any(|(arg_name, _)| *arg_name == "nf");
    let number = if has_nf && has_vm {
        arg_cfg_final.len() - 2
    } else if has_vm {
        arg_cfg_final.len() - 1
    } else {
        arg_cfg_final.len()
    };
    check_args(name, args, number, has_vm)?;
    for (idx, (arg_name, arg_pos)) in arg_cfg_final.iter().rev().enumerate() {
        let value = match *arg_name {
            "rs1" | "rs2" | "rd" => map_x_reg(args[idx], arg_name)?,
            "vs1" | "vs2" | "vs3" | "vd" => map_v_reg(args[idx], arg_name)?,
            "simm5" => {
                let arg_current = args[idx].to_lowercase();
                let value = if arg_current.starts_with('-') {
                    let value = if let Some(content) = arg_current.strip_prefix("0x") {
                        i8::from_str_radix(content, 16)
                            .map_err(|_| anyhow!("Parse simm5 value failed: {}", arg_current))?
                    } else {
                        arg_current
                            .parse::<i8>()
                            .map_err(|_| anyhow!("Parse simm5 value failed: {}", arg_current))?
                    };
                    if value < -16 || value > 15 {
                        return Err(anyhow!(
                            "Simm5 value out of range: {} expected: [-16, 15]",
                            value
                        ));
                    }
                    value as u8
                } else {
                    let value = if let Some(content) = arg_current.strip_prefix("0x") {
                        u8::from_str_radix(content, 16)
                            .map_err(|_| anyhow!("Parse uimm5 value failed: {}", arg_current))?
                    } else {
                        arg_current
                            .parse::<u8>()
                            .map_err(|_| anyhow!("Parse uimm5 value failed: {}", arg_current))?
                    };
                    if value > 31 {
                        return Err(anyhow!(
                            "Uimm5 value out of range: {} expected: [0, 31]",
                            value
                        ));
                    }
                    value
                };
                (value & 0b00011111) as u32
            }
            "zimm" => {
                let value = args[idx]
                    .parse::<u8>()
                    .map_err(|_| anyhow!("Parse zimm5 value failed: {}", args[idx]))?;
                if value > 31 {
                    return Err(anyhow!(
                        "zimm5 value out of range: {} expected: [0, 31]",
                        value
                    ));
                }
                (value as u8 & 0b00011111) as u32
            }
            // NOTE: special case
            "zimm10" | "zimm11" => {
                let mut vsew: u8 = 0;
                let mut lmul = Vlmul::M1;
                let mut ta = false;
                let mut ma = false;
                let mut tu = false;
                let mut mu = false;
                for arg_str in &args[idx..] {
                    if *arg_str == "ta" {
                        ta = true;
                    } else if *arg_str == "ma" {
                        ma = true;
                    } else if *arg_str == "tu" {
                        tu = true;
                    } else if *arg_str == "mu" {
                        mu = true;
                    } else if arg_str.as_bytes()[0] == b'e' {
                        let sew = arg_str[1..]
                            .parse::<u16>()
                            .map_err(|_| anyhow!("Invalid SEW value format: {}", arg_str))?;
                        vsew = match sew {
                            8 => 0,
                            16 => 1,
                            32 => 2,
                            64 => 3,
                            128 => 4,
                            256 => 5,
                            512 => 6,
                            1024 => 7,
                            _ => {
                                return Err(anyhow!(
                                    "Invalid SEW value for vtypei: {}, arg: {}",
                                    sew,
                                    arg_str
                                ))
                            }
                        };
                    } else if arg_str.as_bytes()[0] == b'm' {
                        lmul = Vlmul::from_str(arg_str)
                            .ok_or_else(|| anyhow!("Invalid LMUL value format: {}", arg_str))?;
                    } else {
                        return Err(anyhow!(
                            "Invalid argument for {}, expected: e{{n}}/m{{n}}/ta/ma/tu/mu, got: {}",
                            name,
                            arg_str
                        ));
                    }
                }

                if ta && tu {
                    return Err(anyhow!("ta/tu can not both exists"));
                }
                if ma && mu {
                    return Err(anyhow!("ma/mu can not both exists"));
                }

                let mut value = lmul as u8;
                value |= vsew << 3;
                if ta {
                    value |= 1 << 6;
                }
                if ma {
                    value |= 1 << 7;
                }
                value as u32
            }
            // See comment in asm.pest
            "vm" => {
                if args.get(idx) == Some(&"v0.t") {
                    0
                } else {
                    1
                }
            }
            // FIXME: support segment load/store
            "nf" => 0,
            // FIXME: support `Zvamo`
            "wd" => return Err(anyhow!("Zvamo instructions are not supported.")),
            _ => unreachable!(),
        };
        base |= value << arg_pos;
    }
    Ok(base)
}

#[repr(u8)]
enum Vlmul {
    // LMUL=1/8
    Mf8 = 0b101,
    // LMUL=1/4
    Mf4 = 0b110,
    // LMUL=1/2
    Mf2 = 0b111,
    // LMUL=1
    M1 = 0b000,
    // LMUL=2
    M2 = 0b001,
    // LMUL=4
    M4 = 0b010,
    // LMUL=8
    M8 = 0b011,
}

impl Vlmul {
    fn from_str(name: &str) -> Option<Vlmul> {
        match name {
            "mf8" => Some(Vlmul::Mf8),
            "mf4" => Some(Vlmul::Mf4),
            "mf2" => Some(Vlmul::Mf2),
            "m1" => Some(Vlmul::M1),
            "m2" => Some(Vlmul::M2),
            "m4" => Some(Vlmul::M4),
            "m8" => Some(Vlmul::M8),
            _ => None,
        }
    }
}

fn check_args(name: &str, args: &[&str], number: usize, vm: bool) -> Result<(), Error> {
    if V0_TAIL_INSTS.contains(&name) {
        if args.len() != number + 1 {
            return Err(anyhow!(
                "Invalid number of arguments for {}, expected: {}, got: {}",
                name,
                number + 1,
                args.len()
            ));
        }
        if args[args.len() - 1] != "v0" {
            return Err(anyhow!("The last argument of {} must be v0", name));
        }
        return Ok(());
    }
    let (expected, min, max) = if name == "vsetvli" || name == "vsetivli" {
        ("3 <= n <=6".to_string(), 3, 6)
    } else if !vm {
        (number.to_string(), number, number)
    } else {
        (format!("{} or {}", number, number + 1), number, number + 1)
    };
    if args.len() < min || args.len() > max {
        Err(anyhow!(
            "Invalid number of arguments for {}, expected: {}, got: {}",
            name,
            expected,
            args.len()
        ))
    } else {
        Ok(())
    }
}

fn map_v_reg(name: &str, label: &str) -> Result<u32, Error> {
    if name.as_bytes()[0] != b'v' {
        return Err(anyhow!("Invalid {} V register: {}", label, name));
    }
    let number = name[1..]
        .parse::<u32>()
        .map_err(|_| anyhow!("Invalid {} V register: {}", label, name))?;
    if number > 31 {
        return Err(anyhow!("Invalid {} V register: {}", label, name));
    }
    Ok(number)
}

fn map_x_reg(name: &str, label: &str) -> Result<u32, Error> {
    match name {
        "x0" | "zero" => Ok(0),
        "x1" | "ra" => Ok(1),
        "x2" | "sp" => Ok(2),
        "x3" | "gp" => Ok(3),
        "x4" | "tp" => Ok(4),
        "x5" | "t0" => Ok(5),
        "x6" | "t1" => Ok(6),
        "x7" | "t2" => Ok(7),
        "x8" | "s0" | "fp" => Ok(8),
        "x9" | "s1" => Ok(9),
        "x10" | "a0" => Ok(10),
        "x11" | "a1" => Ok(11),
        "x12" | "a2" => Ok(12),
        "x13" | "a3" => Ok(13),
        "x14" | "a4" => Ok(14),
        "x15" | "a5" => Ok(15),
        "x16" | "a6" => Ok(16),
        "x17" | "a7" => Ok(17),
        "x18" | "s2" => Ok(18),
        "x19" | "s3" => Ok(19),
        "x20" | "s4" => Ok(20),
        "x21" | "s5" => Ok(21),
        "x22" | "s6" => Ok(22),
        "x23" | "s7" => Ok(23),
        "x24" | "s8" => Ok(24),
        "x25" | "s9" => Ok(25),
        "x26" | "s10" => Ok(26),
        "x27" | "s11" => Ok(27),
        "x28" | "t3" => Ok(28),
        "x29" | "t4" => Ok(29),
        "x30" | "t5" => Ok(30),
        "x31" | "t6" => Ok(31),
        _ => Err(anyhow!("Invalid {} X register: {}", label, name)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_riscvgc() {
        assert_eq!(encode("add {abc_t}, {abc}, 3", false).unwrap(), None);
    }

    fn assert_inst(code: u32, inst: &str) {
        let output_code = encode(inst, false).unwrap().unwrap();
        assert_eq!(output_code, code, "0b{:032b} - {}", output_code, inst);
    }

    // # configuration setting
    // # https://github.com/riscv/riscv-v-spec/blob/master/vcfg-format.adoc
    //
    // vsetivli     31=1 30=1 zimm10    zimm 14..12=0x7 rd 6..0=0x57
    // vsetvli      31=0 zimm11          rs1 14..12=0x7 rd 6..0=0x57
    // vsetvl       31=1 30..25=0x0 rs2  rs1 14..12=0x7 rd 6..0=0x57
    #[test]
    fn test_vset() {
        for (code, inst) in [
            (0b10000001111110011111001011010111, "vsetvl x5, s3, t6"),
            (0b00000000000010011111001011010111, "vsetvli x5, s3, e8"),
            (
                0b00000010101010011111001011010111,
                "vsetvli x5, s3, e256, m4",
            ),
            (
                0b00001110101010011111001011010111,
                "vsetvli x5, s3, e256, m4, ta, ma",
            ),
            (
                0b11000010101010011111001011010111,
                "vsetivli x5, 19, e256, m4",
            ),
            (
                0b11000010101010011111001011010111,
                "vsetivli x5, 19, e256, m4, tu, mu",
            ),
            (
                0b11001010101010011111001011010111,
                "vsetivli x5, 19, e256, m4, tu, ma",
            ),
            (
                0b11000110101010011111001011010111,
                "vsetivli x5, 19, e256, m4, ta, mu",
            ),
            (
                0b11001110101010011111001011010111,
                "vsetivli x5, 19, e256, m4, ta, ma",
            ),
        ] {
            assert_inst(code, inst);
        }
    }

    #[test]
    fn test_simm5_range() {
        for (code, inst) in [
            (0b00000010001010000011000011010111, "vadd.vi  v1, v2, -16"),
            (0b00000010001001111011000011010111, "vadd.vi  v1, v2, 15"),
        ] {
            assert_inst(code, inst);
        }

        assert!(encode("vadd.vi  v1, v2, -17", false).is_err());
    }

    // vlm.v          31..28=0      27..26=0 25=1 24..20=0xb  rs1 14..12=0x0  vd 6..0=0x07
    // vle8.v         nf       28=0 27..26=0 vm   24..20=0    rs1 14..12=0x0  vd 6..0=0x07
    // vle8ff.v       nf       28=0 27..26=0 vm   24..20=0x10 rs1 14..12=0x0  vd 6..0=0x07
    // vl1re8.v       31..29=0 28=0 27..26=0 25=1 24..20=0x08 rs1 14..12=0x0  vd 6..0=0x07
    #[test]
    fn test_rs1_vd_0x07() {
        for (code, inst) in [
            // vlm.v     vd, (rs1)
            (0b00000010101100101000000010000111, "vlm.v v1, (t0)"),
            // vle8.v    vd, (rs1), vm
            (0b00000010000000101000000010000111, "vle8.v v1, (t0)"),
            // vle8ff.v  vd, (rs1), vm
            (0b00000011000000101000000010000111, "vle8ff.v v1, (t0)"),
            // vl1re8.v  vd, (rs1)
            (0b00000010100000101000000010000111, "vl1re8.v v1, (t0)"),
        ] {
            assert_inst(code, inst);
        }
    }
    // vsm.v          31..28=0      27..26=0 25=1 24..20=0xb  rs1 14..12=0x0 vs3 6..0=0x27
    // vse8.v         nf       28=0 27..26=0 vm   24..20=0    rs1 14..12=0x0 vs3 6..0=0x27
    // vs1r.v         31..29=0 28=0 27..26=0 25=1 24..20=0x08 rs1 14..12=0x0 vs3 6..0=0x27
    #[test]
    fn test_rs1_vs3_0x27() {
        for (code, inst) in [
            // vsm.v     vs3, (rs1)
            (0b00000010101100101000000010100111, "vsm.v v1, (t0)"),
            // vse8.v    vs3, (rs1), vm
            (0b00000010000000101000000010100111, "vse8.v v1, (t0)"),
            // vs1r.v    vs3, (rs1)
            (0b00000010100000101000000010100111, "vs1r.v v1, (t0)"),
        ] {
            assert_inst(code, inst);
        }
    }

    // vluxei8.v  nf 28=0 27..26=1 vm vs2 rs1 14..12=0x0  vd 6..0=0x07
    // vloxei8.v  nf 28=0 27..26=3 vm vs2 rs1 14..12=0x0  vd 6..0=0x07
    #[test]
    fn test_vs2_rs1_vd_0x07() {
        for (code, inst) in [
            // vluxei8.v    vd, (rs1), vs2, vm
            (0b00000110001000101000000010000111, "vluxei8.v v1, (t0), v2"),
            // vloxei8.v    vd, (rs1), vs2, vm
            (0b00001110001000101000000010000111, "vloxei8.v v1, (t0), v2"),
        ] {
            assert_inst(code, inst);
        }
    }
    // vsuxei8.v      nf 28=0 27..26=1 vm vs2 rs1 14..12=0x0 vs3 6..0=0x27
    // vsoxei8.v      nf 28=0 27..26=3 vm vs2 rs1 14..12=0x0 vs3 6..0=0x27
    #[test]
    fn test_vs2_rs1_vs3_0x27() {
        for (code, inst) in [
            // vsuxei8.v   vs3, (rs1), vs2, vm
            (0b00000110001000101000000010100111, "vsuxei8.v v1, (t0), v2"),
            // vsoxei8.v   vs3, (rs1), vs2, vm
            (0b00001110001000101000000010100111, "vsoxei8.v v1, (t0), v2"),
        ] {
            assert_inst(code, inst);
        }
    }

    // vlse8.v         nf 28=0 27..26=2 vm rs2 rs1 14..12=0x0  vd 6..0=0x07
    #[test]
    fn test_rs2_rs1_vd_0x07() {
        // vlse8.v    vd, (rs1), rs2, vm
        assert_inst(0b00001010011000101000000010000111, "vlse8.v v1, (t0), t1");
    }

    // vsse8.v         nf 28=0 27..26=2 vm rs2 rs1 14..12=0x0 vs3 6..0=0x27
    #[test]
    fn test_rs2_rs1_vs3_0x27() {
        // vsse8.v    vs3, (rs1), rs2, vm
        assert_inst(0b00001010011000101000000010100111, "vsse8.v v1, (t0), t1");
    }

    // vfadd.vf       31..26=0x00 vm   vs2 rs1 14..12=0x5 vd 6..0=0x57
    // vfmerge.vfm    31..26=0x17 25=0 vs2 rs1 14..12=0x5 vd 6..0=0x57
    // vmacc.vx       31..26=0x2d vm   vs2 rs1 14..12=0x6 vd 6..0=0x57
    #[test]
    fn test_vs2_rs1_vd_0x57() {
        for (code, inst) in [
            // vfadd.vf    vd, vs2, rs1, vm
            (0b00000010001000101101000011010111, "vfadd.vf v1, v2, t0"),
            // vfmerge.vfm vd, vs2, rs1, v0
            (
                0b01011100001000101101000011010111,
                "vfmerge.vfm v1, v2, t0, v0",
            ),
            // vmacc.vx vd, rs1, vs2, vm
            (0b10110110000101100110000111010111, "vmacc.vx v3, a2, v1"),
        ] {
            assert_inst(code, inst);
        }
    }

    // vfmv.s.f       31..26=0x10 25=1 24..20=0 rs1 14..12=0x5 vd 6..0=0x57
    // vmv.v.x        31..26=0x17 25=1 24..20=0 rs1 14..12=0x4 vd 6..0=0x57
    #[test]
    fn test_rs1_vd_0x57() {
        for (code, inst) in [
            // vfmv.s.f vd, rs1
            (0b01000010000000101101000011010111, "vfmv.s.f v1, t0"),
            // vmv.v.x  vd, rs1
            (0b01011110000000101100000011010111, "vmv.v.x v1, t0"),
        ] {
            assert_inst(code, inst);
        }
    }

    // vfadd.vv       31..26=0x00 vm   vs2 vs1 14..12=0x1 vd 6..0=0x57
    // vadc.vvm       31..26=0x10 25=0 vs2 vs1 14..12=0x0 vd 6..0=0x57
    // vmacc.vv       31..26=0x2d vm   vs2 vs1 14..12=0x2 vd 6..0=0x57
    #[test]
    fn test_vs2_vs1_vd_0x57() {
        for (code, inst) in [
            // vfadd.vv   vd, vs2, vs1, vm
            (0b00000010001000011001000011010111, "vfadd.vv v1, v2, v3"),
            // vadc.vvm   vd, vs2, vs1, v0
            (
                0b01000000001000011000000011010111,
                "vadc.vvm v1, v2, v3, v0",
            ),
            // vmacc.vv vd, vs1, vs2, vm
            (0b10110110001000001010000111010111, "vmacc.vv v3, v1, v2"),
        ] {
            assert_inst(code, inst);
        }
    }

    // vfmv.f.s       31..26=0x10 25=1 vs2 19..15=0    14..12=0x1 rd 6..0=0x57
    // vcpop.m        31..26=0x10 vm   vs2 19..15=0x10 14..12=0x2 rd 6..0=0x57
    #[test]
    fn test_vs2_rd_0x57() {
        // vfmv.f.s rd, vs2
        // vcpop.m  rd, vs2, vm
        for (code, inst) in [
            (0b01000010001000000001001011010111, "vfmv.f.s t0, v2"),
            (0b01000010001010000010001011010111, "vcpop.m t0, v2"),
        ] {
            assert_inst(code, inst);
        }
    }

    // vfcvt.xu.f.v     31..26=0x12 vm   vs2 19..15=0x00 14..12=0x1 vd 6..0=0x57
    // vmv1r.v          31..26=0x27 25=1 vs2 19..15=0    14..12=0x3 vd 6..0=0x57
    #[test]
    fn test_vs2_vd_0x57() {
        for (code, inst) in [
            // vfcvt.xu.f.v vd, vs2, vm
            (0b01001010001000000001000011010111, "vfcvt.xu.f.v v1, v2"),
            // vmv<nr>r.v   vd, vs2
            (0b10011110001000000011000011010111, "vmv1r.v v1, v2"),
        ] {
            assert_inst(code, inst);
        }
    }

    // vmv.v.v        31..26=0x17 25=1 24..20=0 vs1 14..12=0x0 vd 6..0=0x57
    #[test]
    fn test_vs1_vd_0x57() {
        // vmv.v.v vd, vs1
        assert_inst(0b01011110000000010000000011010111, "vmv.v.v v1, v2");
    }

    // vadd.vi        31..26=0x00 vm   vs2 simm5 14..12=0x3 vd 6..0=0x57
    // vadc.vim       31..26=0x10 25=0 vs2 simm5 14..12=0x3 vd 6..0=0x57
    #[test]
    fn test_vs2_simm5_vd_0x57() {
        for (code, inst) in [
            // vadd.vi    vd, vs2, imm, vm
            (0b00000010001011011011000011010111, "vadd.vi  v1, v2, -5"),
            // vadc.vim   vd, vs2, imm, v0
            (0b01000000001000101011000011010111, "vadc.vim v1, v2, 5, v0"),
        ] {
            assert_inst(code, inst);
        }
    }

    // vmv.v.i        31..26=0x17 25=1 24..20=0 simm5 14..12=0x3 vd 6..0=0x57
    #[test]
    fn test_simm5_vd_0x57() {
        // vmv.v.i vd, imm
        assert_inst(0b01011110000000101011000011010111, "vmv.v.i v1, 0x5");
    }
    // vid.v          31..26=0x14 vm 24..20=0 19..15=0x11 14..12=0x2 vd 6..0=0x57
    #[test]
    fn test_vd_0x57() {
        // vid.v vd, vm
        assert_inst(0b01010010000010001010000011010111, "vid.v v1");
    }
}
