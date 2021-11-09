use std::fmt::Display;
use std::mem;
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{quote, quote_spanned};
use quote::ToTokens;
use syn::{parse_macro_input, parse_quote};
use syn::{Attribute, Expr, ExprBlock, ExprCall, ExprMacro, Ident, Item, ItemFn, Path};
use syn::fold::{self, Fold};
use syn::spanned::Spanned;

#[derive(Clone)]
struct Folder {
    /// The path to the subject function, as specified in the attribute.
    subject_function_path: Path,

    /// A description of the nearest enclosing conditional.  For our purposes, "conditional"
    /// includes any construct that might cause a piece of code to be skipped or to be evaluated
    /// more than one time.  This includes `if`, but also `loop` and closures, among others.  The
    /// subject function must be called exactly once, so if the call occurs inside a conditional,
    /// we report an error.
    enclosing_conditional_kind: Option<&'static str>,

    /// Span of the first call to the subject function.  `None` if no call has occurred yet.  This
    /// is used for error reporting when there is more than one call.
    first_call_span: Option<Span>,

    /// Whether we're building the spec copy of the function.  If `false`, we're building the test
    /// copy instead.  A few transforms apply even to the test copy, to ensure its behavior remains
    /// consistent with the spec copy.
    spec_mode: bool,

    /// Whether to allow macro expressions in the function body.  By default, macros are forbidden,
    /// since we can't check the macro's expansion for forbidden expressions.
    allow_macros: bool,
}

fn report_error(span: Span, msg: impl Display) -> Expr {
    let msg = msg.to_string();
    let tokens = quote_spanned!(span=> compile_error!(#msg));
    syn::parse2::<ExprMacro>(tokens).unwrap().into()
}

impl Folder {
    fn fold_cond(&mut self, i: Expr, kind: &'static str) -> Expr {
        let old_kind = mem::replace(&mut self.enclosing_conditional_kind, Some(kind));
        let i = fold::fold_expr(self, i);
        self.enclosing_conditional_kind = old_kind;
        i
    }

    fn handle_call(&mut self, call: ExprCall) -> Expr {
        // Check whether this is a call to the subject function.
        match *call.func {
            Expr::Path(ref x) if x.path == self.subject_function_path => {},
            _ => return fold::fold_expr_call(self, call).into(),
        }

        // This check must happen first, so that `self.first_call_span` is set even when other
        // errors occur.  If `first_call_span` is unset, then any errors produced will be replaced
        // with the "couldn't find a call" error.
        if self.first_call_span.is_some() {
            return report_error(call.span(), format_args!(
                "found multiple calls to {}", self.subject_function_path.to_token_stream(),
            ));
        } else {
            self.first_call_span = Some(call.span());
        }

        if let Some(kind) = self.enclosing_conditional_kind {
            return report_error(call.span(), format_args!(
                "call to {} may not occur inside {}",
                self.subject_function_path.to_token_stream(),
                kind,
            ));
        }

        let path = &self.subject_function_path;
        let add_args = call.args.iter().map(|arg| {
            quote!(__crux_msb.add_arg(&(#arg));)
        }).collect::<Vec<_>>();
        let plain_args = call.args.iter().cloned().collect::<Vec<_>>();
        let tokens = if self.spec_mode {
            let func_name_str = format!("{}_result", path.segments.last().unwrap().ident);
            quote_spanned!(call.span()=> {
                let __crux_func = #path;
                __crux_msb = crucible::method_spec::MethodSpecBuilder::new(__crux_func);
                #(#add_args)*
                __crux_msb.gather_assumes();
                let result = if false {
                    // Force the output of `Symbolic::symbolic` to unify with the return type of
                    // the original function call.
                    __crux_func(#(#plain_args),*)
                } else {
                    crucible::Symbolic::symbolic(#func_name_str)
                };
                // TODO: is it correct to call `set_return` this early?
                __crux_msb.set_return(&result);
                result
            })
        } else {
            quote_spanned!(call.span()=> {
                #call
            })
        };
        syn::parse2::<ExprBlock>(tokens).unwrap().into()
    }
}

impl Fold for Folder {
    fn fold_item(&mut self, i: Item) -> Item {
        // Don't recurse into items that appear inside the function body.
        i
    }

    fn fold_expr(&mut self, i: Expr) -> Expr {
        match i {
            Expr::Async(x) => report_error(x.span(), "async expressions are not supported"),
            Expr::Await(x) => report_error(x.span(), "await expressions are not supported"),
            Expr::Return(x) => report_error(x.span(), "early return is not supported"),
            Expr::Try(x) => report_error(x.span(), "early return is not supported"),
            Expr::Yield(x) => report_error(x.span(), "early return is not supported"),
            Expr::Verbatim(x) => report_error(x.span(), "unparsed expressions are not supported"),

            Expr::Macro(x) => {
                // Whitelist crux-mir macros
                let mut allowed = false;
                if let Some(seg) = x.mac.path.segments.last() {
                    let ident = seg.ident.to_string();
                    match &ident as &str {
                        "crucible_assert" |
                        "crucible_assume" => {
                            allowed = true;
                        },
                        _ => {},
                    }
                }

                if !self.allow_macros && !allowed {
                    report_error(x.span(), "macro expressions are not supported")
                } else {
                    Expr::Macro(fold::fold_expr_macro(self, x))
                }
            },

            // Closures count as conditionals since they might not be called, or might be called
            // more than once.
            Expr::Closure(..) => self.fold_cond(i, "closure"),
            Expr::ForLoop(..) => self.fold_cond(i, "loop"),
            Expr::If(..) => self.fold_cond(i, "conditional"),
            Expr::Loop(..) => self.fold_cond(i, "loop"),
            Expr::Match(..) => self.fold_cond(i, "conditional"),
            // Try blocks count as conditional since they can exit early.
            Expr::TryBlock(..) => self.fold_cond(i, "try block"),
            Expr::While(..) => self.fold_cond(i, "loop"),

            Expr::Call(x) => self.handle_call(x),

            // List of all Expr variants that are known to be safe.  Any new variants added in the
            // future will be caught by the default case.
            Expr::Array(..) |
            Expr::Assign(..) |
            Expr::AssignOp(..) |
            // Async
            // Await
            Expr::Binary(..) |
            Expr::Block(..) |
            Expr::Box(..) |
            Expr::Break(..) |
            // Call
            Expr::Cast(..) |
            // Closure
            Expr::Continue(..) |
            Expr::Field(..) |
            // ForLoop
            Expr::Group(..) |
            // If
            Expr::Index(..) |
            Expr::Let(..) |
            Expr::Lit(..) |
            // Loop
            // Macro
            // Match
            Expr::MethodCall(..) |
            Expr::Paren(..) |
            Expr::Path(..) |
            Expr::Range(..) |
            Expr::Reference(..) |
            Expr::Repeat(..) |
            // Return
            Expr::Struct(..) |
            // Try
            // TryBlock
            Expr::Tuple(..) |
            Expr::Type(..) |
            Expr::Unary(..) |
            Expr::Unsafe(..) => fold::fold_expr(self, i),
            // Verbatim
            // While
            // Yield

            _ => {
                report_error(i.span(), "unknown expression kind")
            },
        }
    }
}

#[proc_macro_attribute]
pub fn crux_spec_for(args: TokenStream, input: TokenStream) -> TokenStream {
    let args = parse_macro_input!(args as Path);
    let func = parse_macro_input!(input as ItemFn);
    let func_span = func.span();

    let folder = Folder {
        subject_function_path: args,
        enclosing_conditional_kind: None,
        first_call_span: None,
        spec_mode: false,
        // TODO: add an option to enable allow_macros
        allow_macros: false,
    };

    let mut test_func = func.clone();
    {
        let mut folder = Folder {
            spec_mode: false,
            ..folder.clone()
        };
        let block = Box::new(folder.fold_block(*test_func.block));

        if folder.first_call_span.is_none() {
            let expr = report_error(func_span, format_args!(
                "couldn't find a call to {}",
                folder.subject_function_path.to_token_stream(),
            ));
            return quote_spanned! { func_span=>
                #expr ;
            }.into();
        }

        let block = parse_quote!({
            crucible::method_spec::clobber_globals();
            #block
        });
        test_func.block = Box::new(block);

        let test_attr: Attribute = parse_quote!(#[crux_test]);
        test_func.attrs.push(test_attr);
    }

    let mut spec_func = func;
    {
        let mut folder = Folder {
            spec_mode: true,
            ..folder
        };
        let block = Box::new(folder.fold_block(*spec_func.block));
        assert!(
            folder.first_call_span.is_some(),
            "first folder found a call but second folder didn't?",
        );

        let block = parse_quote!({
            let mut __crux_msb: crucible::method_spec::MethodSpecBuilder;
            #block
            __crux_msb.gather_asserts();
            __crux_msb.finish()
        });
        spec_func.block = Box::new(block);

        spec_func.sig.ident = Ident::new(
            &format!("{}_spec", spec_func.sig.ident),
            spec_func.sig.ident.span(),
        );
        spec_func.sig.output = parse_quote!(-> crucible::method_spec::MethodSpec);
    }

    let tokens = quote! {
        #test_func
        #spec_func
    };
    eprintln!("output = {}", tokens);
    tokens.into()
}
