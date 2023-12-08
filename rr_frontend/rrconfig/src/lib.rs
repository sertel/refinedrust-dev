// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
use config::{Config, Environment, File, FileFormat};
use std::env;
use std::{sync::RwLock, path::PathBuf};
use serde::Deserialize;
use lazy_static::lazy_static;

pub mod launch;
pub mod arg_value;

lazy_static! {
    // Is this RwLock<..> necessary?
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
                .set_default("admit_proofs", false)?;

            // 2. Override with the optional TOML file "RefinedRust.toml" (if there is any)
            builder = builder.add_source(
                File::new("RefinedRust.toml", FileFormat::Toml).required(false)
            );

            // 3. Override with an optional TOML file specified by the `RR_CONFIG` env variable
            if let Ok(file) = env::var("RR_CONFIG") {
                // Since this file is explicitly specified by the user, it would be
                // nice to tell them if we cannot open it.
                builder = builder.add_source(File::with_name(&file));
            }

            // 4. Override with env variables (`RR_QUIET`, ...)
            let builder = builder.add_source(
                Environment::with_prefix("RR")
                    .ignore_empty(true)
            );

            builder.build()
        };
        mk_config().unwrap()
    });
}

/// Generate a dump of the settings
pub fn dump() -> String {
    format!("{:#?}", SETTINGS.read().unwrap())
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
    SETTINGS
        .write()
        .unwrap()
        .set(key, value)
        .unwrap_or_else(|e| panic!("Failed to write setting {key} due to {e}"));
}

/// Should we dump debug files?
pub fn dump_debug_info() -> bool {
    read_setting("dump_debug_info")
}

/// Should we dump borrowck info?
pub fn dump_borrowck_info() -> bool {
    read_setting("dump_borrowck_info")
}

/// In which folder should we store log/dumps?
pub fn log_dir() -> PathBuf {
    PathBuf::from(read_setting::<String>("log_dir"))
}

/// The hotword with which specification attributes should begin.
pub fn spec_hotword() -> String {
    read_setting("spec_hotword")
}

/// Should we hide user messages?
pub fn quiet() -> bool {
    read_setting("quiet")
}

/// Skip features that are unsupported or partially supported
pub fn skip_unsupported_features() -> bool {
    read_setting("skip_unsupported_features")
}

/// Which attribute parser to use? Currently, only the "verbose" parser is supported.
pub fn attribute_parser() -> String {
    read_setting("attribute_parser")
}

/// Which directory to write the generated Coq files to?
pub fn output_dir() -> Option<String> {
    read_optional_setting("output_dir")
}

/// Whether to admit proofs of functions instead of running Qed. 
pub fn admit_proofs() -> bool {
    read_setting("admit_proofs")
}

/// Which file to read shims from?
pub fn shim_file() -> Option<String> {
    read_optional_setting("shims")
}

/// Run the proof checker after generating the Coq code?
pub fn check_proofs() -> bool {
    read_setting("run_check")
}

/// Which cargo to use?
pub fn cargo_path() -> String {
    read_setting("cargo_path")
}

/// Which cargo command should cargo-refinedrust hook into?
pub fn cargo_command() -> String {
    read_setting("cargo_command")
}

/// Should refinedrust-rustc behave like rustc?
pub fn be_rustc() -> bool {
    read_setting("be_rustc")
}

/// Should also dependencies be verified?
pub fn verify_deps() -> bool {
    read_setting("verify_deps")
}

/// Should verification be skipped?
pub fn no_verify() -> bool {
    read_setting("no_verify")
}
pub fn set_no_verify(value: bool) {
    write_setting("no_verify", value);
}

/// Should we check for overflows?
pub fn check_overflows() -> bool {
    read_setting("check_overflows")
}
