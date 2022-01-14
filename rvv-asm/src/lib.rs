extern crate proc_macro;

use anyhow::Error;
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::ext::IdentExt;
use syn::parse::{Parse, ParseStream};
use syn::parse_macro_input;
use syn::punctuated::Punctuated;

/// Convert RISC-V Vector Extension to `.byte 0x00, 0x11, 0xaa, 0xbb` format asm instructions.
///
/// ## Example:
/// Compile will fail due to target not supported on develop/CI machine.
/// ```compile_fail
/// let lo: i64;
/// unsafe {
///     rvv_asm::rvv_asm!(
///         "vsetvl x5, s3, t6",
///         "1: vle256.v v3, (a0), vm",
///         "2:",
///         "li {lo}, 4",
///         lo = out(reg) lo,
///     );
/// }
/// ```
#[proc_macro]
pub fn rvv_asm(item: TokenStream) -> TokenStream {
    transform(item, false)
}

/// Convert **reserved only** RISC-V Vector Extension to `.byte 0x00, 0x11, 0xaa, 0xbb` format asm instructions.
#[proc_macro]
pub fn rvv_asm_reserved_only(item: TokenStream) -> TokenStream {
    transform(item, true)
}

fn transform(item: TokenStream, reserved_only: bool) -> TokenStream {
    let items = parse_macro_input!(item as Items);
    let mut insts = Vec::new();
    let mut args: Option<TokenStream2> = None;
    for item in items.inner {
        match item {
            Item::LitStr(content) => {
                for part in content.value().split('\n') {
                    // For support inline label
                    insts.extend(part.split_inclusive(':').map(|s| s.to_string()));
                }
            }
            Item::Args(tokens) => {
                if args.is_some() {
                    panic!("Args between string literal is not allowed");
                }
                args = Some(tokens);
            }
        }
    }
    let insts_str = insts.iter().map(|s| s.as_str()).collect::<Vec<_>>();
    TokenStream::from(rvv_asm_inner(&insts_str, args.as_ref(), reserved_only).unwrap())
}

fn rvv_asm_inner(
    insts: &[&str],
    args: Option<&TokenStream2>,
    reserved_only: bool,
) -> Result<TokenStream2, Error> {
    let insts_out = insts
        .iter()
        .map(|inst| {
            let out = rvv_encode::encode(inst, reserved_only)?
                .map(|code| {
                    let [b0, b1, b2, b3] = code.to_le_bytes();
                    format!(".byte {:#04x}, {:#04x}, {:#04x}, {:#04x}", b0, b1, b2, b3)
                })
                .unwrap_or_else(|| inst.to_string());
            Ok(out)
        })
        .collect::<Result<Vec<_>, Error>>()?;
    let rest_args = args.cloned().unwrap_or_else(TokenStream2::new);
    Ok(quote! {
        asm!(
            #(#insts_out,)*
            #rest_args
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
        assert_eq!(
            rvv_asm_inner(&["vsetvl x5, s3, t6"], None, false)
                .unwrap()
                .to_string(),
            quote!(asm!(".byte 0xd7, 0xf2, 0xf9, 0x81",);).to_string()
        );
    }

    #[test]
    fn test_vle_n_v() {
        assert_eq!(
            rvv_asm_inner(&["vle128.v v3, (a0), v0.t"], None, false)
                .unwrap()
                .to_string(),
            quote!(asm!(".byte 0x87, 0x01, 0x05, 0x10",);).to_string()
        );
    }

    #[test]
    fn test_vse_n_v() {
        assert_eq!(
            rvv_asm_inner(&["vse1024.v v3, (a0)"], None, false)
                .unwrap()
                .to_string(),
            quote!(asm!(".byte 0xa7, 0x71, 0x05, 0x12",);).to_string()
        );
    }

    #[test]
    fn test_multi_asm() {
        let expected_output = quote! {
            asm!(
                ".byte 0xd7, 0xf2, 0xf9, 0x81",
                "li {0}, 3",
                "1: ",
                "apple_pie:",
                "li {1}, 4",
                in (reg) a ,
                out (reg) hi ,
            );
        };
        assert_eq!(
            rvv_asm_inner(
                &[
                    "vsetvl x5, s3, t6",
                    "li {0}, 3",
                    "1: ",
                    "apple_pie:",
                    "li {1}, 4",
                ],
                Some(&quote! {
                    in(reg) a,
                    out(reg) hi,
                }),
                false,
            )
            .unwrap()
            .to_string(),
            expected_output.to_string()
        );
    }

    #[test]
    fn test_multi_asm_named() {
        let expected_output = quote! {
            asm!(
                ".byte 0xd7, 0xf2, 0xf9, 0x81",
                "1: ",
                "li {a}, 3",
                "apple_pie:",
                "li {hi}, 4",
                a = in (reg) a ,
                hi = out (reg) hi ,
            );
        };
        assert_eq!(
            rvv_asm_inner(
                &[
                    "vsetvl x5, s3, t6",
                    "1: ",
                    "li {a}, 3",
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
