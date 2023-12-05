fn main() {
    #[cfg(feature = "debug")]
    println!("cargo:rustc-cfg=debug_assertions");
}
