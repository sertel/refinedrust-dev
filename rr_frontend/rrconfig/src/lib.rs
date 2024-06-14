// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cell::RefCell;
use std::path::PathBuf;
use std::sync::RwLock;
use std::{env, mem};

use config::{Config, Environment, File, FileFormat};
use lazy_static::lazy_static;
use path_clean::PathClean;
use serde::Deserialize;

pub mod arg_value;
pub mod launch;

lazy_static! {
    // RwLock due to rustc parallelism
    static ref SETTINGS: RwLock<Config> = RwLock::new({
        let mk_config = || {
            let mut builder = Config::builder();

            // 1. Default values
            builder = builder.set_default("be_rustc", false)?
                .set_default("log_dir", "./log/")?
                .set_default("check_overflows", true)?
                .set_default("dump_debug_info", false)?
                .set_default("dump_borrowck_info", false)?
                .set_default("quiet", false)?
                .set_default("skip_unsupported_features", true)?
                .set_default("spec_hotword", "rr")?
                .set_default("attribute_parser", "verbose")?
                .set_default("run_check", false)?
                .set_default("verify_deps", false)?
                .set_default("no_verify", false)?
                .set_default("cargo_path", "cargo")?
                .set_default("cargo_command", "check")?
                .set_default("admit_proofs", false)?
                .set_default("generate_dune_project", true)?
                .set_default("lib_load_paths", Vec::<String>::new())?
                .set_default("work_dir", ".")?;

            // 2. Override with the optional TOML file "RefinedRust.toml" (if there is any)
            builder = builder.add_source(
                File::new("RefinedRust.toml", FileFormat::Toml).required(false)
            );

            // 3. Override with an optional TOML file specified by the `RR_CONFIG` env variable
            if let Ok(file) = env::var("RR_CONFIG") {
                // Since this file is explicitly specified by the user, it would be
                // nice to tell them if we cannot open it.
                builder = builder.add_source(File::with_name(&file));

                // set override for workdir to the config file path
                let path_to_file = PathBuf::from(file);
                let filepath = path_to_file.parent().unwrap().to_str().unwrap();

                builder = builder.set_default("work_dir", filepath)?;
            }

            // 4. Override with env variables (`RR_QUIET`, ...)
            let builder = builder.add_source(
                Environment::with_prefix("RR").ignore_empty(true)
            );

            builder.build()
        };

        mk_config().unwrap()
    });
}

/// Generate a dump of the settings
#[must_use]
pub fn dump() -> String {
    format!("{:#?}", SETTINGS.read().unwrap())
}

/// Makes the path absolute with respect to the `work_dir`.
fn make_path_absolute(path: &str) -> PathBuf {
    // read the base path we set
    let base_path = work_dir();

    let path_buf = PathBuf::from(path);
    if path_buf.is_absolute() {
        path_buf
    } else {
        let base_path_buf = PathBuf::from(base_path);
        if base_path_buf.is_absolute() {
            base_path_buf.join(path_buf).clean()
        } else {
            env::current_dir().unwrap().join(base_path_buf).join(path_buf).clean()
        }
    }
}

fn read_optional_setting<T>(name: &'static str) -> Option<T>
where
    T: Deserialize<'static>,
{
    SETTINGS.read().unwrap().get(name).ok()
}

fn read_setting<T>(name: &'static str) -> T
where
    T: Deserialize<'static>,
{
    read_optional_setting(name).unwrap_or_else(|| panic!("Failed to read setting {:?}", name))
}

fn write_setting<T: Into<config::Value>>(key: &'static str, value: T) {
    let builder = Config::builder().set_override(key, value).unwrap();
    let mut w = SETTINGS.write().unwrap();
    let old_settings = mem::take(&mut *w);
    let new_settings = builder.add_source(old_settings).build().unwrap();
    *w = new_settings;
}

#[must_use]
pub fn work_dir() -> String {
    read_setting("work_dir")
}

#[must_use]
pub fn absolute_work_dir() -> PathBuf {
    let s = work_dir();
    make_path_absolute(&s)
}

/// Should we dump debug files?
#[must_use]
pub fn dump_debug_info() -> bool {
    read_setting("dump_debug_info")
}

/// Should we dump borrowck info?
#[must_use]
pub fn dump_borrowck_info() -> bool {
    read_setting("dump_borrowck_info")
}

/// In which folder should we store log/dumps?
#[must_use]
pub fn log_dir() -> PathBuf {
    make_path_absolute(&read_setting::<String>("log_dir"))
}

/// Get the paths in which to search for `RefinedRust` library declarations.
#[must_use]
pub fn lib_load_paths() -> Vec<PathBuf> {
    let mut paths = Vec::new();
    let s = read_setting::<Vec<String>>("lib_load_paths");
    for p in s {
        paths.push(make_path_absolute(&p));
    }
    paths
}

/// The hotword with which specification attributes should begin.
#[must_use]
pub fn spec_hotword() -> String {
    read_setting("spec_hotword")
}

/// Should we hide user messages?
#[must_use]
pub fn quiet() -> bool {
    read_setting("quiet")
}

/// Skip features that are unsupported or partially supported
#[must_use]
pub fn skip_unsupported_features() -> bool {
    read_setting("skip_unsupported_features")
}

/// Whether to generate a dune-project file for this project
#[must_use]
pub fn generate_dune_project() -> bool {
    read_setting("generate_dune_project")
}

/// Which attribute parser to use? Currently, only the "verbose" parser is supported.
#[must_use]
pub fn attribute_parser() -> String {
    read_setting("attribute_parser")
}

/// Which directory to write the generated Coq files to?
#[must_use]
pub fn output_dir() -> Option<PathBuf> {
    read_optional_setting("output_dir").map(|s: String| make_path_absolute(&s))
}

/// Whether to admit proofs of functions instead of running Qed.
#[must_use]
pub fn admit_proofs() -> bool {
    read_setting("admit_proofs")
}

/// Post-generation hook
#[must_use]
pub fn post_generation_hook() -> Option<String> {
    read_optional_setting("post_generation_hook")
}

/// Which file to read shims from?
#[must_use]
pub fn shim_file() -> Option<PathBuf> {
    read_optional_setting("shims").map(|s: String| make_path_absolute(&s))
}

/// Which file should we read extra specs from?
#[must_use]
pub fn extra_specs_file() -> Option<PathBuf> {
    read_optional_setting("extra_specs").map(|s: String| make_path_absolute(&s))
}

/// Run the proof checker after generating the Coq code?
#[must_use]
pub fn check_proofs() -> bool {
    read_setting("run_check")
}

/// Which cargo to use?
#[must_use]
pub fn cargo_path() -> String {
    read_setting("cargo_path")
}

/// Which cargo command should cargo-refinedrust hook into?
#[must_use]
pub fn cargo_command() -> String {
    read_setting("cargo_command")
}

/// Should refinedrust-rustc behave like rustc?
#[must_use]
pub fn be_rustc() -> bool {
    read_setting("be_rustc")
}

/// Should also dependencies be verified?
#[must_use]
pub fn verify_deps() -> bool {
    read_setting("verify_deps")
}

/// Should verification be skipped?
#[must_use]
pub fn no_verify() -> bool {
    read_setting("no_verify")
}

pub fn set_no_verify(value: bool) {
    write_setting("no_verify", value);
}

/// Should we check for overflows?
#[must_use]
pub fn check_overflows() -> bool {
    read_setting("check_overflows")
}

#[cfg(test)]
mod tests {
    use super::*;

    // NOTE: These tests SHOULD NOT use the same key as the same SETTINGS variable is used

    #[test]
    fn read_default() {
        assert_eq!(read_setting::<String>("work_dir"), ".");
    }

    #[test]
    fn read_env() {
        env::set_var("RR_simple_read", "true");

        assert!(read_setting::<bool>("simple_read"));
    }

    #[test]
    fn read_env_case() {
        env::set_var("RR_CaSe_ChEcK", "true");

        assert!(read_setting::<bool>("case_check"));
    }

    #[test]
    fn read_env_value_bool() {
        env::set_var("RR_CaSe_ChEcK", "1");

        assert!(read_setting::<bool>("case_check"));
    }

    #[test]
    fn write() {
        write_setting("key", true);

        assert!(read_setting::<bool>("key"));

        write_setting("key", false);

        assert!(!(read_setting::<bool>("key")));
    }

    #[test]
    fn write_merge() {
        write_setting("key1", "value1");
        write_setting("key2", "value2");

        assert_eq!(read_setting::<String>("key1"), "value1");
        assert_eq!(read_setting::<String>("key2"), "value2");
    }
}
