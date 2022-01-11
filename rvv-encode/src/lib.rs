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

pub fn inst_code(inst: &str) -> Result<Option<u32>, Error> {
    let pairs = if let Ok(result) = AsmParser::parse(Rule::inst, inst.trim()) {
        result
    } else {
        let _ = AsmParser::parse(Rule::label, inst.trim())
            .map_err(|err| anyhow!("parse asm error: {}", err))?;
        return Ok(None);
    };
    let mut name = "unknown";
    let mut args = Vec::new();
    for pair in pairs {
        for inner1_pair in pair.into_inner() {
            match inner1_pair.as_rule() {
                Rule::inst_name => {
                    name = inner1_pair.as_str();
                }
                Rule::inst_arg => {
                    for inner2_pair in inner1_pair.into_inner() {
                        match inner2_pair.as_rule() {
                            Rule::inst_arg_simple | Rule::integer => {
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
    let has_vm = arg_cfg.iter().any(|(arg_name, _)| *arg_name == "vm");
    let has_nf = arg_cfg.iter().any(|(arg_name, _)| *arg_name == "nf");
    let number = if has_nf && has_vm {
        arg_cfg.len() - 2
    } else if has_vm {
        arg_cfg.len() - 1
    } else {
        arg_cfg.len()
    };
    check_args(name, args, number, has_vm)?;
    for (idx, (arg_name, arg_pos)) in arg_cfg.iter().rev().enumerate() {
        let value = match *arg_name {
            "rs1" | "rs2" | "rd" => map_x_reg(args[idx], arg_name)?,
            "vs1" | "vs2" | "vs3" | "vd" => map_v_reg(args[idx], arg_name)?,
            "simm5" => {
                let value = args[idx]
                    .parse::<i8>()
                    .map_err(|_| anyhow!("Parse simm5 value failed: {}", args[idx]))?;
                if value < -15 || value > 16 {
                    return Err(anyhow!(
                        "Simm5 value out of range: {} expected: [-15, 16]",
                        value
                    ));
                }
                (value as u8 & 0b00011111) as u32
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
                for arg_str in &args[idx..] {
                    if *arg_str == "ta" {
                        ta = true;
                    } else if *arg_str == "ma" {
                        ma = true;
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
                            "Invalid argument for {}, expected: e{{n}}/m{{n}}/ta/ma, got: {}",
                            name,
                            arg_str
                        ));
                    }
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
            "vm" => {
                if args.get(idx) == Some(&"vm") {
                    1
                } else {
                    0
                }
            }
            // FIXME: support segment load/store
            "nf" => 0,
            // FIXME: support `Zvamo`
            "wd" => 0,
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
    fn test_vsetvl() {
        assert_eq!(
            inst_code("vsetvl x5, s3, t6").unwrap(),
            Some(0b10000001111110011111001011010111)
        );
        assert_eq!(
            inst_code("vsetvli x5, s3, e8").unwrap(),
            Some(0b00000000000010011111001011010111)
        );
        assert_eq!(
            inst_code("vsetvli x5, s3, e256, m4").unwrap(),
            Some(0b00000010101010011111001011010111)
        );
        assert_eq!(
            inst_code("vsetvli x5, s3, e256, m4, ta, ma").unwrap(),
            Some(0b00001110101010011111001011010111)
        );
        assert_eq!(
            inst_code("vsetivli x5, 19, e256, m4").unwrap(),
            Some(0b11000010101010011111001011010111)
        );
    }

    #[test]
    fn test_vle_n_v() {
        assert_eq!(
            inst_code("vle64.v v3, (a0), vm").unwrap(),
            Some(0b00000010000001010111000110000111)
        );
    }

    #[test]
    fn test_vse_n_v() {
        assert_eq!(
            inst_code("vse64.v v3, (a0), vm").unwrap(),
            Some(0b00000010000001010111000110100111)
        );
    }
}
