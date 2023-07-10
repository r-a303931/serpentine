#![feature(proc_macro_diagnostic)]

extern crate proc_macro;

use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{
    parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    token, Expr, Ident, LitStr, Result, Token, Type,
};

mod kw {
    syn::custom_keyword!(local);
    syn::custom_keyword!(optional);
    syn::custom_keyword!(rest);
    syn::custom_keyword!(Symbol);
    syn::custom_keyword!(Bool);
    syn::custom_keyword!(Int);
    syn::custom_keyword!(Float);
    syn::custom_keyword!(String);
    syn::custom_keyword!(List);
    syn::custom_keyword!(Callable);
    syn::custom_keyword!(Error);
    syn::custom_keyword!(Foreign);
}

enum LispType {
    Symbol(kw::Symbol),
    Bool(kw::Bool),
    Int(kw::Int),
    Float(kw::Float),
    String(kw::String),
    List(kw::List),
    Callable(kw::Callable),
    Error(kw::Error),
    Foreign(kw::Foreign),
}

impl Parse for LispType {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(kw::Symbol) {
            Ok(LispType::Symbol(input.parse()?))
        } else if lookahead.peek(kw::Bool) {
            Ok(LispType::Bool(input.parse()?))
        } else if lookahead.peek(kw::Int) {
            Ok(LispType::Int(input.parse()?))
        } else if lookahead.peek(kw::Float) {
            Ok(LispType::Float(input.parse()?))
        } else if lookahead.peek(kw::String) {
            Ok(LispType::String(input.parse()?))
        } else if lookahead.peek(kw::List) {
            Ok(LispType::List(input.parse()?))
        } else if lookahead.peek(kw::Callable) {
            Ok(LispType::Callable(input.parse()?))
        } else if lookahead.peek(kw::Error) {
            Ok(LispType::Error(input.parse()?))
        } else if lookahead.peek(kw::Foreign) {
            Ok(LispType::Foreign(input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

enum ArgAttr {
    Optional(Token![&]),
    Rest(Token![&]),
}

impl ArgAttr {
    fn is_optional(&self) -> bool {
        matches!(self, ArgAttr::Optional(_))
    }

    fn is_rest(&self) -> bool {
        matches!(self, ArgAttr::Rest(_))
    }

    fn and(&self) -> &Token![&] {
        match self {
            Self::Rest(and) => and,
            Self::Optional(and) => and,
        }
    }
}

struct ArgDefinition {
    modifier: Option<ArgAttr>,
    name: Ident,
    argtype: Option<Ident>,
}

impl Parse for ArgDefinition {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        let modifier = if lookahead.peek(Token![&]) {
            let and: Token![&] = input.parse()?;
            let lookahead = input.lookahead1();
            if lookahead.peek(kw::optional) {
                let _: kw::optional = input.parse()?;
                Some(ArgAttr::Optional(and))
            } else if lookahead.peek(kw::rest) {
                let _: kw::rest = input.parse()?;
                Some(ArgAttr::Rest(and))
            } else {
                Err(lookahead.error())?
            }
        } else {
            None
        };

        let name = input.parse()?;

        let lookahead = input.lookahead1();
        let argtype = if lookahead.peek(Token![:]) {
            let _: Token![:] = input.parse()?;
            Some(input.parse()?)
        } else {
            None
        };

        Ok(ArgDefinition {
            modifier,
            name,
            argtype,
        })
    }
}

struct FunctionType {
    local: Option<kw::local>,
    is_async: Option<Token![async]>,
    name: Ident,
    name_internal: LitStr,
    ctx: Option<(Ident, Type)>,
    pos_name: Ident,
    env_name: Ident,
    args: Punctuated<ArgDefinition, Token![,]>,
    docstring: Option<LitStr>,
    body: Expr,
}

impl Parse for FunctionType {
    fn parse(input: ParseStream) -> Result<Self> {
        let local = input.parse()?;
        let is_async = input.parse()?;
        let name = input.parse()?;
        let name_internal = input.parse()?;
        let content;
        let _: token::Paren = parenthesized!(content in input);
        let pos_or_ctx_name: Ident = content.parse()?;
        let lookahead = content.lookahead1();
        let (ctx, pos_name) = if lookahead.peek(Token![:]) {
            let _: Token![:] = content.parse()?;
            let atype = content.parse()?;
            let _: Token![,] = content.parse()?;
            (Some((pos_or_ctx_name, atype)), content.parse()?)
        } else {
            (None, pos_or_ctx_name)
        };
        let _: Token![,] = content.parse()?;
        let env_name = content.parse()?;
        let _: Option<Token![,]> = content.parse()?;
        let args = content.parse_terminated(ArgDefinition::parse)?;
        let docstring = input.parse()?;
        let body = input.parse()?;

        Ok(Self {
            local,
            is_async,
            name,
            name_internal,
            ctx,
            pos_name,
            env_name,
            args,
            docstring,
            body,
        })
    }
}

/// Procedural macro to generate functions that can be brought
/// into the serpentine execution environment
///
/// # Function structure
///
/// (local?) (async?) function_name "internal-name" (position, environment, arg1(: type?)) ("doc string"?) body
///
/// - Local is used for functions internal to serpentine. Do not use outside of
///   the serpentine crate
/// - Async declares the function as async and allows using .await inside the
///   function block
/// - Function name represents the name of the struct that will be created as a
///   pointer to the function body
/// - "internal-name" is how the function expects to be called from within the environment
/// - position represents the name of the parameter that will hold a reference to the
///   parameter
#[proc_macro]
pub fn declare_lisp_func(input: TokenStream) -> TokenStream {
    let FunctionType {
        local,
        is_async,
        name,
        name_internal,
        ctx,
        pos_name,
        env_name,
        args,
        docstring,
        body,
        ..
    } = parse_macro_input!(input as FunctionType);

    let name_str = LitStr::new(
        &name.span().unwrap().source_text().unwrap_or_default(),
        name.span(),
    );

    let is_local = local.is_some();
    let lisprs = (if is_local {
        quote! { crate }
    } else {
        quote! { ::serpentine_macro }
    })
    .to_token_stream();

    let (ctx_name, ctx_type): (proc_macro2::TokenStream, proc_macro2::TokenStream) = match ctx {
        Some((name, typ)) => (quote! { #name }, quote! { #typ }),
        None => (quote! { __hidden_ctx }, quote! { () }),
    };

    let args_len = args.len();

    if let Some(arg) = args
        .iter()
        .enumerate()
        .find(|(i, arg)| match &arg.modifier {
            Some(modifier) => modifier.is_rest() && *i != args_len - 1,
            None => false,
        })
    {
        arg.1.modifier.as_ref().unwrap().and().spans[0]
            .unstable()
            .error("rest attribute can only be applied to the last argument")
            .emit();
        return TokenStream::new();
    }

    fn translate_optional_arg(
        name_str: &LitStr,
        lisprs: &proc_macro2::TokenStream,
        name: &Ident,
        atype: &Option<Ident>,
    ) -> proc_macro2::TokenStream {
        let match_stmt = match atype {
            Some(argtype) => {
                let argtype_str = LitStr::new(
                    &argtype.span().unwrap().source_text().unwrap_or_default(),
                    argtype.span(),
                );

                quote! {
                    match &**item {
                        #lisprs::vm::LispValue::Nil | #lisprs::vm::LispValue::#argtype(_) => {
                            item
                        },
                        _ => {
                            return Err(RuntimeError::new(
                                RuntimeErrorKind::InvalidArgument(
                                    format!("expected {}, got {}", #argtype_str, item.get_pretty_name()).into()
                                ),
                                #name_str.into(),
                                __hidden_ctx.1.clone(),
                            ));
                        }
                    }
                }.to_token_stream()
            }
            None => quote! {
                item
            }
            .to_token_stream(),
        };

        quote! {
            let #name = {
                use #lisprs::vm::error::{RuntimeError, RuntimeErrorKind};

                let item = match __hidden_args_iter.next() {
                    None => return Err(RuntimeError::new(
                        RuntimeErrorKind::InvalidArgument(
                            "not enough arguments to call function".into()
                        ),
                        #name_str.into(),
                        __hidden_ctx.1.clone(),
                    )),
                    Some(t) => t
                };

                #match_stmt
            };
        }
        .to_token_stream()
    }

    fn translate_rest_arg(name: &Ident) -> proc_macro2::TokenStream {
        quote! {
            let #name = __hidden_args_iter.collect::<Vec<_>>();
        }
    }

    fn translate_regular_arg(
        name_str: &LitStr,
        lisprs: &proc_macro2::TokenStream,
        name: &Ident,
        atype: &Option<Ident>,
    ) -> proc_macro2::TokenStream {
        let match_stmt = match atype {
            Some(argtype) => {
                let argtype_str = LitStr::new(
                    &argtype.span().unwrap().source_text().unwrap_or_default(),
                    argtype.span(),
                );

                quote! {
                    if let #lisprs::vm::LispValue::#argtype(value) = &**item {
                        value
                    } else {
                        return Err(RuntimeError::new(
                            RuntimeErrorKind::InvalidArgument(
                                format!("expected {}, got {}", #argtype_str, item.get_pretty_name()).into()
                            ),
                            #name_str.into(),
                            __hidden_base_ctx.1.clone(),
                        ));
                    }
                }
                .to_token_stream()
            }
            None => quote! {
                &*item
            }
            .to_token_stream(),
        };

        quote! {
            let #name = {
                use #lisprs::vm::error::{RuntimeError, RuntimeErrorKind};

                let item = match __hidden_args_iter.next() {
                    None => return Err(RuntimeError::new(
                        RuntimeErrorKind::InvalidArgument(
                            "not enough arguments to call function".into()
                        ),
                        #name_str.into(),
                        __hidden_base_ctx.1.clone(),
                    )),
                    Some(t) => match &**t {
                        #lisprs::vm::LispValue::Nil => return Err(RuntimeError::new(
                            RuntimeErrorKind::InvalidArgument(
                                "argument cannot be nil".into()
                            ),
                            #name_str.into(),
                            __hidden_base_ctx.1.clone(),
                        )),
                        _ => t
                    }
                };

                #match_stmt
            };
        }
    }

    let args_stream: proc_macro2::TokenStream = args
        .into_iter()
        .map(|arg| -> TokenStream {
            if arg.modifier.as_ref().map(|m| m.is_optional()) == Some(true) {
                translate_optional_arg(&name_str, &lisprs, &arg.name, &arg.argtype).into()
            } else if arg.modifier.as_ref().map(|m| m.is_rest()) == Some(true) {
                if let Some(argtype) = arg.argtype {
                    argtype
                        .span()
                        .unstable()
                        .warning("argument type is ignored for rest argument")
                        .emit();
                }

                translate_rest_arg(&arg.name).into()
            } else {
                translate_regular_arg(&name_str, &lisprs, &arg.name, &arg.argtype).into()
            }
        })
        .collect::<TokenStream>()
        .into();

    let docs = match docstring {
        Some(docs) => quote! {
            fn docs(&self) -> Option<Arc<str>> {
                Some(Arc::from(#docs))
            }
        },
        None => quote! {
            fn docs(&self) -> Option<Arc<str>> {
                None
            }
        },
    };

    match is_async {
        Some(_async) => quote! {
            #[allow(non_camel_case_types)]
            struct #name;

            unsafe impl Send for #name {}
            unsafe impl Sync for #name {}

            impl #name {
                fn new() -> #lisprs::vm::Callable<#ctx_type> {
                    #lisprs::vm::Callable::AsyncNativeFunc(#name_internal, Arc::new(Self))
                }
            }

            impl std::fmt::Debug for #name {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                    write!(f, "<internal function: {}>", #name_str)
                }
            }

            impl #lisprs::vm::LispAsyncNativeFunc<#ctx_type> for #name {
                fn run<'life0, 'life1, 'life2, 'async_trait>(
                    &'life0 self,
                    ctx: (&'life1 #ctx_type, &'life2 Position),
                    env: #lisprs::vm::SharedContainer<#lisprs::vm::Environment<#ctx_type>>,
                    args: Vec<std::sync::Arc<LispValue<#ctx_type>>>
                ) -> ::core::pin::Pin<Box<dyn ::core::future::Future<Output = Result<std::sync::Arc<LispValue<#ctx_type>>, RuntimeError>> + ::core::marker::Send + 'async_trait>>
                where
                    'life0: 'async_trait,
                    'life1: 'async_trait,
                    'life2: 'async_trait,
                    Self: 'async_trait
                {
                    async fn run(
                        __hidden_base_ctx: (&#ctx_type, &#lisprs::Position),
                        #env_name: #lisprs::vm::SharedContainer<#lisprs::vm::Environment<#ctx_type>>,
                        __hidden_args: Vec<std::sync::Arc<#lisprs::vm::LispValue<#ctx_type>>>
                    ) -> Result<std::sync::Arc<LispValue<#ctx_type>>, RuntimeError> {
                        use #lisprs::vm::error::{RuntimeError, RuntimeErrorKind};

                        let (#ctx_name, #pos_name) = __hidden_base_ctx;
                        let mut __hidden_args_iter = __hidden_args.iter();

                        #args_stream

                        Ok(#body)
                    }

                    Box::pin(run(ctx, env, args))
                }

                #docs
            }
        }.into(),
        None => quote! {
            #[allow(non_camel_case_types)]
            struct #name;

            unsafe impl Send for #name {}
            unsafe impl Sync for #name {}

            impl #name {
                fn new() -> #lisprs::vm::Callable<#ctx_type> {
                    #lisprs::vm::Callable::NativeFunc(#name_internal, Arc::new(Self))
                }
            }

            impl std::fmt::Debug for #name {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                    write!(f, "<internal function: {}>", #name_str)
                }
            }

            impl #lisprs::vm::LispNativeFunc<#ctx_type> for #name {
                fn run(
                    &self,
                    __hidden_base_ctx: (&#ctx_type, &#lisprs::Position),
                    #env_name: #lisprs::vm::SharedContainer<#lisprs::vm::Environment<#ctx_type>>,
                    __hidden_args: Vec<std::sync::Arc<#lisprs::vm::LispValue<#ctx_type>>>
                ) -> Result<std::sync::Arc<#lisprs::vm::LispValue<#ctx_type>>, #lisprs::vm::error::RuntimeError> {
                    use #lisprs::vm::error::{RuntimeError, RuntimeErrorKind};

                    let (#ctx_name, #pos_name) = __hidden_base_ctx;
                    let mut __hidden_args_iter = __hidden_args.iter();

                    #args_stream

                    Ok(#body)
                }

                #docs
            }
        }.into()
    }
}
