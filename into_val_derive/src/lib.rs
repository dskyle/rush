extern crate proc_macro;
extern crate syn;

#[macro_use]
extern crate quote;

use proc_macro::TokenStream;

#[proc_macro_derive(IntoVal)]
pub fn into_val(input: TokenStream) -> TokenStream {
    let s = input.to_string();
    let ast = syn::parse_macro_input(&s).unwrap();

    let gen = into_val_impl(&ast);

    gen.parse().unwrap()
}

fn into_val_impl(ast: &syn::MacroInput) -> quote::Tokens {
    match ast.body {
        syn::Body::Enum(ref variants) => {
            into_val_enum_impl(&ast.ident, variants)
        },
        syn::Body::Struct(..) => unimplemented!(),
    }
}

fn into_val_enum_impl(name: &syn::Ident, variants: &Vec<syn::Variant>) -> quote::Tokens {
    let matches: Vec<quote::Tokens> = variants.iter().map(|var| {
        let vname = &var.ident;
        match var.data {
            syn::VariantData::Struct(ref fields) => {
                let fields: Vec<quote::Tokens> = fields.iter().map(|ref fld| {
                    let id = fld.ident.as_ref().unwrap().clone();
                    quote!{ #id }
                }).collect();
                let fields2 = fields.clone();
                let fields3 = fields.clone();
                quote! {
                    #name::#vname{#(#fields),*} => {
                        Val::Tup(vec![Val::Str(stringify!(#vname).into()),
                          #(Val::Tup(vec![Val::Str(stringify!(#fields2).into()), #fields3.into()])),*])
                    }
                }
            },
            syn::VariantData::Tuple(ref fields) => {
                let fields: Vec<quote::Tokens> = fields.iter().enumerate().map(|(num, _)| {
                    let id = syn::Ident::new(format!("f{}", num));
                    quote!{ #id }
                }).collect();
                let fields2 = fields.clone();
                quote! {
                    #name::#vname(#(#fields),*) => {
                        Val::Tup(vec![Val::Str(stringify!(#vname).into()),
                          #(#fields2.into()),*])
                    }
                }
            },
            syn::VariantData::Unit => {
                quote! {
                    #name::#vname => {
                        Val::Str(stringify!(#name).into()),
                    }
                }
            }
        }
    }).collect();
    quote! {
        impl IntoVal for #name {
            fn into_val(self) -> Val {
                match self {
                    #(#matches),*
                }
            }
        }
    }
}
