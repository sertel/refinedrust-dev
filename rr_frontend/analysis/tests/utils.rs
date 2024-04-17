#[allow(clippy::option_env_unwrap)]
pub fn find_sysroot() -> String {
    // Taken from https://github.com/Manishearth/rust-clippy/pull/911.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));

    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .or_else(|| {
                option_env!("RUST_SRC_PATH")
                    .map(|s| s.strip_suffix("lib/rustlib/rustc-src/rust/compiler/rustc_driver/Cargo.toml"))
                    .flatten()
            })
            .expect(
                "Need to specify RUST_SYSROOT or RUST_SRC_PATH environment variables, or use rustup or multirust",
            )
            .to_owned(),
    }
}
