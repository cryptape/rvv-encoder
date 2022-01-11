extern crate proc_macro;

use anyhow::Error;
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::format_ident;
use quote::quote;
use syn::ext::IdentExt;
use syn::parse::{Parse, ParseStream};
use syn::parse_macro_input;
use syn::punctuated::Punctuated;

#[proc_macro]
pub fn rvv_asm(item: TokenStream) -> TokenStream {
    let items = parse_macro_input!(item as Items);
    let (insts, args) = parse_tokens(items);
    let insts_str = insts.iter().map(|s| s.as_str()).collect::<Vec<_>>();
    TokenStream::from(rvv_asm_inner(&insts_str, args.as_ref(), false).unwrap())
}

#[proc_macro]
pub fn rvv_asm_reserved_only(item: TokenStream) -> TokenStream {
    let items = parse_macro_input!(item as Items);
    let (insts, args) = parse_tokens(items);
    let insts_str = insts.iter().map(|s| s.as_str()).collect::<Vec<_>>();
    TokenStream::from(rvv_asm_inner(&insts_str, args.as_ref(), true).unwrap())
}

fn parse_tokens(items: Items) -> (Vec<String>, Option<TokenStream2>) {
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
    (insts, args)
}

fn rvv_asm_inner(
    insts: &[&str],
    args: Option<&TokenStream2>,
    reserved_only: bool,
) -> Result<TokenStream2, Error> {
    let mut insts_out = Vec::new();
    let mut inst_args_out = Vec::new();
    let mut rvv_inst_idx = 0usize;
    for inst in insts {
        if let Some(code) = rvv_encode::encode(inst, reserved_only)? {
            let [b0, b1, b2, b3] = code.to_le_bytes();
            let var_b0 = format_ident!("_rvv_asm{}", rvv_inst_idx);
            let var_b1 = format_ident!("_rvv_asm{}", rvv_inst_idx + 1);
            let var_b2 = format_ident!("_rvv_asm{}", rvv_inst_idx + 2);
            let var_b3 = format_ident!("_rvv_asm{}", rvv_inst_idx + 3);
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
            insts_out.push(inst.to_string());
        }
    }
    let rest_args = if let Some(args) = args {
        args.clone()
    } else {
        TokenStream2::new()
    };
    Ok(quote! {
        asm!(
            #(#insts_out,)*
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

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_vsetvl() {
        let expected_output = quote! {
            asm!(
                ".byte {_rvv_asm0}, {_rvv_asm1}, {_rvv_asm2}, {_rvv_asm3}",
                _rvv_asm0 = const 215u8,
                _rvv_asm1 = const 242u8,
                _rvv_asm2 = const 249u8,
                _rvv_asm3 = const 129u8,
            );
        };
        assert_eq!(
            rvv_asm_inner(&["vsetvl x5, s3, t6"], None, false)
                .unwrap()
                .to_string(),
            expected_output.to_string()
        );
    }

    #[test]
    fn test_vle_n_v() {
        let expected_output = quote! {
            asm!(
                ".byte {_rvv_asm0}, {_rvv_asm1}, {_rvv_asm2}, {_rvv_asm3}",
                _rvv_asm0 = const 135u8,
                _rvv_asm1 = const 1u8,
                _rvv_asm2 = const 5u8,
                _rvv_asm3 = const 18u8,
            );
        };
        assert_eq!(
            rvv_asm_inner(&["vle128.v v3, (a0), vm"], None, false)
                .unwrap()
                .to_string(),
            expected_output.to_string()
        );
    }

    #[test]
    fn test_vse_n_v() {
        let expected_output = quote! {
            asm!(
                ".byte {_rvv_asm0}, {_rvv_asm1}, {_rvv_asm2}, {_rvv_asm3}",
                _rvv_asm0 = const 167u8,
                _rvv_asm1 = const 113u8,
                _rvv_asm2 = const 5u8,
                _rvv_asm3 = const 16u8,
            );
        };
        assert_eq!(
            rvv_asm_inner(&["vse1024.v v3, (a0)"], None, false)
                .unwrap()
                .to_string(),
            expected_output.to_string()
        );
    }

    #[test]
    fn test_multi_asm() {
        let expected_output = quote! {
            asm!(
                ".byte {_rvv_asm0}, {_rvv_asm1}, {_rvv_asm2}, {_rvv_asm3}" ,
                "li {a}, 3",
                "1: ",
                "apple_pie:",
                "li {hi}, 4",
                a = in (reg) a ,
                hi = out (reg) hi ,
                _rvv_asm0 = const 215u8,
                _rvv_asm1 = const 242u8,
                _rvv_asm2 = const 249u8,
                _rvv_asm3 = const 129u8,
            );
        };
        assert_eq!(
            rvv_asm_inner(
                &[
                    "vsetvl x5, s3, t6",
                    "li {a}, 3",
                    "1: ",
                    "apple_pie:",
                    "li {hi}, 4",
                ],
                Some(&quote! {
                    a = in(reg) a,
                    hi = out(reg) hi,
                }),
                false,
            )
            .unwrap()
            .to_string(),
            expected_output.to_string()
        );
    }
}
