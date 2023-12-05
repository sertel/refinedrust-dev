// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![feature(let_chains)]

//use prusti_utils::{config, launch};
use std::{env, path::PathBuf, process::Command};
use fs_extra::dir::CopyOptions;

use rrconfig::launch as launch;

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
    let rr_target: PathBuf = [cargo_target_path, "verify".to_string()].into_iter().collect();

    let old_output_dir = rrconfig::output_dir();

    let exit_status = Command::new(cargo_path)
        .arg(&command)
        //.args(features)
        .args(args)
        .env("RUST_TOOLCHAIN", launch::get_rust_toolchain_channel())
        .env("RUSTUP_TOOLCHAIN", launch::get_rust_toolchain_channel())
        .env("RUSTC", rr_rustc_path)
        .env("RR_CARGO", "")
        .env("CARGO_TARGET_DIR", &cargo_target)
        // We override the output dir to go to Cargo's target dir
        .env("RR_OUTPUT_DIR", &rr_target)
        // Category B flags (update the docs if any more are added):
        .env("RR_BE_RUSTC", rrconfig::be_rustc().to_string())
        .env("RR_VERIFY_DEPS", rrconfig::verify_deps().to_string())
        // Category A* flags:
        .env("DEFAULT_RR_LOG_DIR", cargo_target.join("log"))
        .status()
        .expect("could not run cargo");

    if exit_status.success() {
        // Optionally, copy to the old output dir
        if let Some(output_dir) = old_output_dir {
            //let output_path = std::path::PathBuf::from(&output_dir);
            //if let Err(_) = fs::read_dir(&output_path) {
                //fs::create_dir_all(output_path).unwrap();
            //}

            let copy_options = CopyOptions::new().content_only(true);
            // TODO: this doesn't work properly currently for workspaces, since we need to resolve
            // the path starting from the root of the workspace
            fs_extra::dir::copy(rr_target, output_dir, &copy_options).unwrap();
        }
        Ok(())

    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
