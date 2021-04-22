use core::cell::UnsafeCell;

/// Load a Cryptol definition.  `module_path` must be the path to a Cryptol module file, and `name`
/// must be an identifier defined within that module.  The type parameter `F` must be a function
/// pointer type matching the type of the Cryptol definition.  For example, if the Cryptol
/// definition has type `[8] -> [8] -> [8]`, then `F` must be `fn(u8, u8) -> u8`, `fn(i8, i8) ->
/// u8`, or some similar combination.
pub fn load<F>(module_path: &str, name: &str) -> F {
    unimplemented!("cryptol::load")
}


#[doc(hidden)]
pub struct SimpleOnce<T>(UnsafeCell<Option<T>>);

unsafe impl<T: Sync> Sync for SimpleOnce<T> {}

impl<T> SimpleOnce<T> {
    pub const fn new() -> SimpleOnce<T> {
        SimpleOnce(UnsafeCell::new(None))
    }
}

impl<T: Sync> SimpleOnce<T> {
    pub fn get_or_init<F: FnOnce() -> T>(&self, f: F) -> &T {
        unsafe {
            let ptr = self.0.get();
            if let Some(ref val) = *ptr {
                val
            } else {
                *ptr = Some(f());
                (*ptr).as_ref().unwrap()
            }
        }
    }
}


#[doc(hidden)]
#[macro_export]
macro_rules! cryptol_function_name {
    ($custom_name:expr, $ident:ident) => { $custom_name };
    ($ident:ident) => { stringify!($ident) };
}

#[macro_export]
macro_rules! cryptol {
    (
        path $path:expr;

        $(
            $pub_:vis fn $name:ident
                ( $($arg_name:ident : $arg_ty:ty),* )
                $( -> $ret_ty:ty )?
                $(= $cryptol_name:expr)?
                ; )*
    ) => {
        $(
            $pub_ fn $name($($arg_name: $arg_ty),*) $(-> $ret_ty)? {
                static FUNC: $crate::cryptol::SimpleOnce<fn($($arg_ty),*) $(-> $ret_ty)?> =
                    $crate::cryptol::SimpleOnce::new();
                let func = FUNC.get_or_init(|| $crate::cryptol::load(
                    $path,
                    $crate::cryptol_function_name!($($cryptol_name,)? $name),
                ));
                func($($arg_name),*)
            }
        )*
    };
}
