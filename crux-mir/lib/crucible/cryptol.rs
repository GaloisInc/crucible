/// Load a Cryptol definition.  `module_path` must be the path to a Cryptol module file, and `name`
/// must be an identifier defined within that module.  The type parameter `F` must be a function
/// pointer type matching the type of the Cryptol definition.  For example, if the Cryptol
/// definition has type `[8] -> [8] -> [8]`, then `F` must be `fn(u8, u8) -> u8`, `fn(i8, i8) ->
/// u8`, or some similar combination.
pub fn load<F>(module_path: &str, name: &str) -> F {
    unimplemented!("cryptol::load")
}
