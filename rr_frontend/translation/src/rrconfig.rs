// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
use config::{Config, File, FileFormat};
use std::collections::HashSet;
use std::env;
use std::sync::RwLock;
use serde::Deserialize;

lazy_static! {
    // Is this RwLock<..> necessary?
    static ref SETTINGS: RwLock<Config> = RwLock::new({
        let mut settings = Config::default();

        // 1. Default values
        //settings.set_default("be_rustc", false).unwrap();
        //settings.set_default("check_overflows", true).unwrap();
        //settings.set_default("check_panics", true).unwrap();
        settings.set_default("log_dir", "./log/").unwrap();
        settings.set_default("output_dir", "./output/").unwrap();
        settings.set_default("dump_debug_info", false).unwrap();
        settings.set_default("dump_borrowck_info", false).unwrap();
        settings.set_default("quiet", false).unwrap();
        settings.set_default("skip_unsupported_features", true).unwrap();
        settings.set_default("spec_hotword", "rr").unwrap();
        settings.set_default("attribute_parser", "verbose").unwrap();
        settings.set_default("shims", None::<String>).unwrap();
        settings.set_default("run_check", false).unwrap();

        // Get the list of all allowed flags.
        let allowed_keys = get_keys(&settings);

        // 2. Override with the optional TOML file "RefinedRust.toml" (if there is any)
        settings.merge(
            File::new("RefinedRust.toml", FileFormat::Toml).required(false)
        ).unwrap();
        check_keys(&settings, &allowed_keys, "RefinedRust.toml file");

        // 3. Override with an optional TOML file specified by the `RR_CONFIG` env variable
        if let Ok(file) = env::var("RR_CONFIG") {
            // Since this file is explicitly specified by the user, it would be
            // nice to tell them if we cannot open it.
            settings.merge(File::with_name(&file)).unwrap();
            check_keys(&settings, &allowed_keys, &format!("{} file", file));
        }

        // 4. Override with env variables (`RR_QUIET`, ...)
        // TODO: I don't know why this panics
        //settings.merge(
            //Environment::with_prefix("RR").ignore_empty(true)
        //).unwrap();
        //check_keys(&settings, &allowed_keys, "environment variables");

         settings
    });
}

fn get_keys(settings: &Config) -> HashSet<String> {
    settings
        .cache
        .clone()
        .into_table()
        .unwrap()
        .into_iter()
        .map(|(key, _)| key)
        .collect()
}

fn check_keys(settings: &Config, allowed_keys: &HashSet<String>, source: &str) {
    for key in settings.cache.clone().into_table().unwrap().keys() {
        if !allowed_keys.contains(key) {
            panic!("{} contains unknown configuration flag: “{}”", source, key);
        }
    }
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

/// Should we dump debug files?
pub fn dump_debug_info() -> bool {
    read_setting("dump_debug_info")
}

/// Should we dump borrowck info?
pub fn dump_borrowck_info() -> bool {
    read_setting("dump_borrowck_info")
}

/// In which folder should we store log/dumps?
pub fn log_dir() -> String {
    read_setting("log_dir")
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
pub fn output_dir() -> String {
    read_setting("output_dir")
}

pub fn shim_file() -> Option<String> {
    read_setting("shims")
}

pub fn check_proofs() -> Option<bool> {
    read_setting("run_check")
}
