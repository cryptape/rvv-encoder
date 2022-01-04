
// vle128.v       nf 28=1 27..26=0 vm 24..20=0 rs1 14..12=0x0  vd 6..0=0x07
extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;

fn rvv_asm_inner(inst: &str) -> proc_macro2::TokenStream {
    quote!{
        asm!("li a7, 3");
    }
}

#[proc_macro]
pub fn rvv_asm(item: TokenStream) -> TokenStream {
    let inst = parse_macro_input!(item as syn::LitStr);
    TokenStream::from(rvv_asm_inner(inst.value().as_str()))
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_test() {
        let expected_output = quote!{
            asm!("li a7, 3");
        };
        assert_eq!(rvv_asm_inner("xx").to_string(), expected_output.to_string());
    }
}
