extern crate proc_macro;
extern crate syn;
#[macro_use]
extern crate quote;

use self::proc_macro::TokenStream;
use self::syn::Ident;

#[proc_macro_derive(Destroy)]
pub fn destroy(input: TokenStream) -> TokenStream {
    let s = input.to_string();
    let ast = syn::parse_derive_input(&s).unwrap();
    let gen = impl_destroy(&ast);
    gen.parse().unwrap()
}

fn impl_destroy(ast: &syn::DeriveInput) -> quote::Tokens {
    let re = regex::Regex::new(r"(?P<c>[A-Z])").unwrap();

    let name = &ast.ident;
    let method_name =
        Ident::new(format!("destroy{}", re.replace_all(&name.to_string(), "_$c")).to_lowercase());

    quote! {
        #[no_mangle]
        pub unsafe extern "C" fn #method_name(
            ptr: *mut #name,
        ) {
            let _ = Box::from_raw(ptr);
        }
    }
}
