extern crate proc_macro;

use anyhow::{anyhow, Error};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::format_ident;
use quote::quote;
use regex::Regex;
use syn::ext::IdentExt;
use syn::parse::{Parse, ParseStream};
use syn::parse_macro_input;
use syn::punctuated::Punctuated;

#[allow(dead_code, clippy::type_complexity)]
mod opcodes;

fn inst_code(inst: &str) -> Result<Option<u32>, Error> {
    let inst_lower = inst.trim().to_lowercase();
    let re_inst = Regex::new(r"(?P<name>\S+)\s+(?P<args>.+)").unwrap();
    let re_args = Regex::new(r"\(?(?P<arg>\w+)\)?,?\s*").unwrap();
    let caps = re_inst
        .captures(&inst_lower)
        .ok_or_else(|| anyhow!("Invalid instruction({}): name not found", inst))?;
    let name = caps.name("name").unwrap().as_str();
    let args = caps.name("args").unwrap().as_str().trim();
    let args_vec = re_args
        .captures_iter(args)
        .map(|caps| caps["arg"].to_owned())
        .collect::<Vec<_>>();

    if let Some((_, base, args_cfg)) = opcodes::INSTRUCTIONS
        .iter()
        .find(|(inst_name, _, _)| *inst_name == name)
    {
        gen_inst_code(name, &args_vec, *base, args_cfg).map(Some)
    } else {
        Ok(None)
    }
}

fn gen_inst_code(
    name: &str,
    args: &[String],
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
            "rs1" | "rs2" | "rd" => map_x_reg(args[idx].as_str(), arg_name)?,
            "vs1" | "vs2" | "vs3" | "vd" => map_v_reg(args[idx].as_str(), arg_name)?,
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
            "vm" => {
                if args.get(idx).map(|s| s.as_str()) == Some("vm") {
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

fn check_args(name: &str, args: &[String], number: usize, vm: bool) -> Result<(), Error> {
    let (expected, min, max) = if !vm {
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

fn rvv_asm_inner(insts: &[String], args: Option<&TokenStream2>) -> Result<TokenStream2, Error> {
    let mut insts_out = Vec::new();
    let mut inst_args_out = Vec::new();
    let mut rvv_inst_idx = 0usize;
    for inst in insts {
        if let Some(code) = inst_code(inst.as_str())? {
            let [b0, b1, b2, b3] = code.to_le_bytes();
            let var_b0 = format_ident!("b{}", rvv_inst_idx);
            let var_b1 = format_ident!("b{}", rvv_inst_idx + 1);
            let var_b2 = format_ident!("b{}", rvv_inst_idx + 2);
            let var_b3 = format_ident!("b{}", rvv_inst_idx + 3);
            rvv_inst_idx += 4;
            insts_out.push(format!(
                ".byte {{{}}}, {{{}}}, {{{}}}, {{{}}}",
                var_b0, var_b1, var_b2, var_b3
            ));
            inst_args_out.push(quote! {
                #var_b0 = const #b0,
                #var_b1 = const #b1,
                #var_b2 = const #b2,
                #var_b3 = const #b3,
            });
        } else {
            insts_out.push(inst.clone());
        }
    }
    let rest_args = if let Some(args) = args {
        args.clone()
    } else {
        TokenStream2::new()
    };
    // println!("insts_out: {:#?}", insts_out);
    // println!("inst_args_out: {:#?}", inst_args_out);
    // println!("rest_args: {:#?}", rest_args);
    Ok(quote! {
        asm!(
            #(
                #insts_out,
            )*
            #rest_args
            #(#inst_args_out)*
        );
    })
}

#[derive(Debug)]
enum Item {
    LitStr(syn::LitStr),
    Args(TokenStream2),
}
#[derive(Debug)]
struct Items {
    inner: Punctuated<Item, syn::token::Comma>,
}
impl Parse for Items {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Items {
            inner: input.parse_terminated(Item::parse)?,
        })
    }
}
impl Parse for Item {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(syn::Ident::peek_any) {
            input.parse().map(Item::Args)
        } else {
            input.parse().map(Item::LitStr)
        }
    }
}

#[proc_macro]
pub fn rvv_asm(item: TokenStream) -> TokenStream {
    let items = parse_macro_input!(item as Items);
    let mut insts = Vec::new();
    let mut args: Option<TokenStream2> = None;
    for item in items.inner {
        match item {
            Item::LitStr(inst) => insts.push(inst.value()),
            Item::Args(tokens) => {
                if args.is_some() {
                    panic!("Args between string literal is not allowed");
                }
                args = Some(tokens);
            }
        }
    }
    TokenStream::from(rvv_asm_inner(&insts, args.as_ref()).unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vsetvl() {
        let expected_output = quote! {
            asm!(
                ".byte {b0}, {b1}, {b2}, {b3}",
                b0 = const 215u8 , b1 = const 242u8 , b2 = const 249u8 , b3 = const 129u8,
            );
        };
        let inst = "vsetvl x5, s3, t6";
        assert_eq!(
            inst_code(inst).unwrap(),
            Some(0b10000001111110011111001011010111)
        );
        assert_eq!(
            rvv_asm_inner(&[inst.to_string()], None)
                .unwrap()
                .to_string(),
            expected_output.to_string()
        );
    }

    #[test]
    fn test_vle_n_v() {
        let expected_output = quote! {
            asm!(
                ".byte {b0}, {b1}, {b2}, {b3}",
                b0 = const 135u8 , b1 = const 1u8 , b2 = const 5u8 , b3 = const 18u8,
            );
        };
        assert_eq!(
            rvv_asm_inner(&["vle128.v v3, (a0), vm".to_string()], None)
                .unwrap()
                .to_string(),
            expected_output.to_string()
        );
        assert_eq!(
            inst_code("vle64.v v3, (a0), vm").unwrap(),
            Some(0b00000010000001010111000110000111)
        );
    }

    #[test]
    fn test_vse_n_v() {
        let expected_output = quote! {
            asm!(
                ".byte {b0}, {b1}, {b2}, {b3}",
                b0 = const 167u8 , b1 = const 113u8 , b2 = const 5u8 , b3 = const 16u8,
            );
        };
        assert_eq!(
            rvv_asm_inner(&["vse1024.v v3, (a0)".to_string()], None)
                .unwrap()
                .to_string(),
            expected_output.to_string()
        );
        assert_eq!(
            inst_code("vse64.v v3, (a0), vm").unwrap(),
            Some(0b00000010000001010111000110100111)
        );
    }
}
