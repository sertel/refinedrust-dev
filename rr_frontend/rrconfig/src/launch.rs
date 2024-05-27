// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![deny(unused_must_use)]
use std::env;
use std::path::PathBuf;
use std::process::Command;

#[must_use]
pub fn get_current_executable_dir() -> PathBuf {
    env::current_exe()
        .expect("current executable path invalid")
        .parent()
        .expect("failed to obtain the folder of the current executable")
        .to_path_buf()
}

/// Append paths to the loader environment variable
pub fn add_to_loader_path(paths: Vec<PathBuf>, cmd: &mut Command) {
    #[cfg(target_os = "windows")]
    const LOADER_PATH: &str = "PATH";
    #[cfg(target_os = "linux")]
    const LOADER_PATH: &str = "LD_LIBRARY_PATH";
    #[cfg(target_os = "macos")]
    const LOADER_PATH: &str = "DYLD_FALLBACK_LIBRARY_PATH";
    env_prepend_path(LOADER_PATH, paths, cmd);
}

/// Prepend paths to an environment variable
fn env_prepend_path(name: &str, value: Vec<PathBuf>, cmd: &mut Command) {
    let old_value = env::var_os(name);
    let mut parts = value;
    if let Some(v) = &old_value {
        parts.extend(env::split_paths(v));
    };
    match env::join_paths(parts) {
        Ok(new_value) => {
            cmd.env(name, new_value);
        },
        Err(err) => panic!("Error: {err:?}"),
    }
}
