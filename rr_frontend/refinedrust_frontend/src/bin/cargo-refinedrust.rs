// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![feature(let_chains)]

//use prusti_utils::{config, launch};
use std::env;
use std::path::PathBuf;
use std::process::Command;

use rrconfig::launch;

fn main() {
    if let Err(code) = process(env::args().skip(1)) {
        std::process::exit(code);
    }
}

fn process<I>(args: I) -> Result<(), i32>
where
    I: Iterator<Item = String>,
{
    // can we make this more robust?
    let mut rr_rustc_path = env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("refinedrust-rustc");
    if cfg!(windows) {
        rr_rustc_path.set_extension("exe");
    }

    // Remove the "refinedrust" argument when `cargo-refinedrust` is invoked as
    // `cargo --cflag prusti -- -Pflag` (note the space in `cargo refinedrust` rather than a `-`)
    let args = args.skip_while(|arg| arg == "refinedrust");
    // Remove the "-- -Pflag" arguments since these won't apply to `cargo check`.
    // They have already been loaded (and the Category B flags are used below).
    let args = args.take_while(|arg| arg != "--");

    // Category B flags (see dev-guide flags table):
    let cargo_path = rrconfig::cargo_path();
    let command = rrconfig::cargo_command();

    // TODO: If we're using workspaces, we should figure out the right dir for the workspace
    let cargo_target_path = env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let cargo_target: PathBuf = [cargo_target_path.to_string()].into_iter().collect();

    let maybe_output_dir = rrconfig::output_dir();
    let output_dir;
    if let Some(old_output_dir) = maybe_output_dir {
        output_dir = old_output_dir;
    } else {
        output_dir = [cargo_target_path, "verify".to_string()].into_iter().collect();
    }

    let exit_status = Command::new(cargo_path)
        .arg(&command)
        //.args(features)
        .args(args)
        .env("RUST_TOOLCHAIN", launch::get_rust_toolchain_channel())
        .env("RUSTUP_TOOLCHAIN", launch::get_rust_toolchain_channel())
        .env("RUSTC", rr_rustc_path)
        .env("RR_CARGO", "")
        .env("CARGO_TARGET_DIR", &cargo_target)
        // We override the output dir
        .env("RR_OUTPUT_DIR", &output_dir)
        // Category B flags (update the docs if any more are added):
        .env("RR_BE_RUSTC", rrconfig::be_rustc().to_string())
        .env("RR_VERIFY_DEPS", rrconfig::verify_deps().to_string())
        // Category A* flags:
        .env("DEFAULT_RR_LOG_DIR", cargo_target.join("log"))
        .status()
        .expect("could not run cargo");

    if exit_status.success() { Ok(()) } else { Err(exit_status.code().unwrap_or(-1)) }
}
