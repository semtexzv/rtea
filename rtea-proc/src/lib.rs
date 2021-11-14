use proc_macro::TokenStream;
use proc_macro::TokenTree::Punct;
use std::str::FromStr;

/// Helper for creating the initialization function for TCL extensions.
///
/// This macro will automatically create the appropriate wrapper to validate
/// the interpreter and "provide" the package to the interpreter.  The
/// prototype of the wrapped function should be ```rust fn
/// (interp: &rtea::Interpreter) -> Result<rtea::TclStatus, String> ``` and
/// one or two attributes should be passed to the macro.  The first must be
/// the module's name with a capital first letter and all others lowercase
/// (this is a TCL requirement).  The second, optional attribute, is the
/// version which by TCL convention should be in accordance with semver.
///
/// # Example
/// ```rust
/// #[module_init(Example, "1.0.0")]
/// fn init(interp: &Interpreter) -> Result<TclStatus, String> {
///     interp.eval("Initializing module...")
/// }
/// ```
///
/// The above example will create a function named `Example_Init` (with the
/// `no_mangle` attribute) which TCL will use as the initialization routine.
/// This assumes that your files final library name matches the expectation
/// of `-lexample` for the C linker (which is the case if used in a "cdylib"
/// crate named "example").
#[proc_macro_attribute]
pub fn module_init(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut mod_name = None;
    let mut version = None;
    for a in attr {
        if let Punct(_) = a {
            continue;
        }
        if mod_name == None {
            mod_name = Some(a.to_string());
        } else if version == None {
            version = Some(a.to_string());
        } else {
            panic!("Unexpected additional attributes to 'module_init': {}", a)
        }
    }
    let mod_name = mod_name.expect("no module name found");
    let version = version.unwrap_or("".to_string());

    let mut out_stream = TokenStream::new();

    let mut next_item = false;
    let mut fn_name = None;
    for i in item {
        if next_item {
            fn_name = Some(i.to_string());
            next_item = false;
        } else if fn_name.is_none() && i.to_string() == "fn" {
            next_item = true;
        }
        out_stream.extend([i]);
    }
    let fn_name = fn_name.expect("'module_init' macro not used on a function");

    out_stream.extend(
        TokenStream::from_str(&format!(
            r#"
                #[no_mangle]
                pub extern "C" fn {module_symbol}_Init(interp: *const Interpreter) -> TclStatus {{
                    Interpreter::from_raw(interp)
                        .map(|interp| {init_fn}(interp)
                            .and(interp.provide_package("{module_tcl}", {version}))
                            .unwrap_or_else(|s| {{interp.set_result(&s); TclStatus::Error}}))
                        .unwrap_or(TclStatus::Error)
                }}
            "#,
            module_symbol = mod_name,
            init_fn = fn_name,
            module_tcl = mod_name.to_lowercase(),
            version = version
        ))
        .unwrap(),
    );

    out_stream
}
