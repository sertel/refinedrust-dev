// This file uses code from the Prusti project under the MPL 2.0 license.
//
// Other parts of the source are © 2023, The RefinedRust Developers and Contributors
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

#![feature(box_patterns)]
#![feature(rustc_private)]
extern crate rustc_borrowck;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;

use std::env;
use std::process::Command;

use log::{debug, info};
use rustc_driver::Compilation;
use rustc_hir::def_id::LocalDefId;
use rustc_interface::Config;
use rustc_middle::query::queries::mir_borrowck;
use rustc_middle::query::{ExternProviders, Providers};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use translation::environment::mir_storage;
use {shlex, translation};

const BUG_REPORT_URL: &str = "https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev/-/issues/new";

fn get_rr_version_info() -> String {
    format!(
        "{}, commit {} {}, built on {}",
        env!("CARGO_PKG_VERSION"),
        option_env!("COMMIT_HASH").unwrap_or("<unknown>"),
        option_env!("COMMIT_TIME").unwrap_or("<unknown>"),
        option_env!("BUILD_TIME").unwrap_or("<unknown>"),
    )
}

/// Callbacks for the RefinedRust frontend.
struct RRCompilerCalls {}

// From Prusti.
fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> mir_borrowck::ProvidedValue<'tcx> {
    let body_with_facts = rustc_borrowck::consumers::get_body_with_borrowck_facts(
        tcx,
        def_id,
        rustc_borrowck::consumers::ConsumerOptions::PoloniusOutputFacts,
    );
    // SAFETY: This is safe because we are feeding in the same `tcx` that is
    // going to be used as a witness when pulling out the data.
    unsafe {
        mir_storage::store_mir_body(tcx, def_id, body_with_facts);
    }
    let mut providers = Providers::default();
    rustc_borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn override_queries(_session: &Session, local: &mut Providers, _: &mut ExternProviders) {
    // overriding these queries makes sure that the `mir_storage` gets all the relevant bodies,
    // also for external crates?
    local.mir_borrowck = mir_borrowck;
    //external.mir_borrowck = mir_borrowck;
}

/// Main entry point to the frontend that is called by the driver.
/// This translates a crate.
pub fn analyze<'tcx>(tcx: TyCtxt<'tcx>) {
    match translation::generate_coq_code(tcx, |vcx| vcx.write_coq_files()) {
        Ok(_) => (),
        Err(e) => {
            println!("Frontend failed with error {:?}", e);
            std::process::exit(1)
        },
    }

    match rrconfig::post_generation_hook() {
        None => (),
        Some(s) => {
            if let Some(parts) = shlex::split(&s) {
                let work_dir = rrconfig::absolute_work_dir();
                let dir_path = std::path::PathBuf::from(&work_dir);
                info!("running post-generation hook in {:?}: {:?}", dir_path, s);

                let status = Command::new(&parts[0])
                    .args(&parts[1..])
                    .current_dir(&dir_path)
                    .status()
                    .expect("failed to execute process");
                println!("Post-generation hook finished with {status}");
            }
        },
    }

    if rrconfig::check_proofs() {
        if cfg!(target_os = "windows") {
            println!("Cannot run proof checker on Windows.");
        } else if let Some(dir_str) = rrconfig::output_dir() {
            let dir_path = std::path::PathBuf::from(&dir_str);

            info!("calling type checker in {:?}", dir_path);

            let status = Command::new("dune")
                .arg("build")
                .current_dir(&dir_path)
                .status()
                .expect("failed to execute process");

            println!("Type checker finished with {status}");
        }
    }
}

impl rustc_driver::Callbacks for RRCompilerCalls {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        if !rrconfig::no_verify() {
            config.override_queries = Some(override_queries);
        }
    }

    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        if !rrconfig::no_verify() {
            // Analyze the crate and inspect the types under the cursor.
            queries.global_ctxt().unwrap().enter(|tcx| {
                analyze(tcx);
            });
            Compilation::Stop
        } else {
            // TODO: We also need this to properly compile deps.
            // However, for deps I'd ideally anyways have be_rustc??
            Compilation::Continue
        }
    }
}

fn main() {
    rustc_driver::install_ice_hook(BUG_REPORT_URL, |_handler| ());

    // If we should act like rustc, just run the main function of the driver
    if rrconfig::be_rustc() {
        rustc_driver::main();
    }

    // otherwise, initialize our loggers
    env_logger::init();

    info!("Getting output dir: {:?}", env::var("RR_OUTPUT_DIR"));

    // This environment variable will not be set when building dependencies.
    let is_primary_package = env::var("CARGO_PRIMARY_PACKAGE").is_ok();
    info!("is_primary_package: {}", is_primary_package);
    // Is this crate a dependency when user doesn't want to verify dependencies
    let is_no_verify_dep_crate = !is_primary_package && !rrconfig::verify_deps();

    // Would `cargo check` not report errors for this crate? That is, are lints disabled
    // (i.e. is this a non-local crate)
    let args = env::args();
    let args: Vec<_> = args.collect();
    let are_lints_disabled =
        rrconfig::arg_value::arg_value(&args, "--cap-lints", |val| val == "allow").is_some();

    if is_no_verify_dep_crate || are_lints_disabled {
        rrconfig::set_no_verify(true);
    }

    let mut rustc_args = vec![];
    let mut is_codegen = false;
    for arg in env::args() {
        if rustc_args.is_empty() {
            // Very first arg: binary name.
            rustc_args.push(arg);
        } else {
            match arg.as_str() {
                _ => {
                    // Disable incremental compilation because it causes mir_borrowck not to be called.
                    if arg == "--codegen" || arg == "-C" {
                        is_codegen = true;
                    } else if is_codegen && arg.starts_with("incremental=") {
                        // Just drop the argument.
                        is_codegen = false;
                    } else {
                        if is_codegen {
                            rustc_args.push("-C".to_owned());
                            is_codegen = false;
                        }
                        rustc_args.push(arg);
                    }
                },
            }
        }
    }
    debug!("rustc arguments: {:?}", rustc_args);

    let exit_code = rustc_driver::catch_with_exit_code(move || {
        if rustc_args.get(1).map(|s| s.as_ref()) == Some("-vV") {
            // When cargo queries the verbose rustc version,
            // also print the RR version to stdout.
            // This ensures that the cargo build cache is
            // invalidated when the RR version changes.
            println!("RefinedRust version: {}", get_rr_version_info());
        }

        // TODO figure out how we can do this such that also normal builds work
        //rustc_args.push("-Zcrate-attr=feature(stmt_expr_attributes)".to_owned());
        //rustc_args.push("-Zcrate-attr=feature(custom_inner_attributes)".to_owned());
        //rustc_args.push("-Zcrate-attr=feature(register_tool)".to_owned());
        //rustc_args.push("-Zcrate-attr=register_tool(rr)".to_owned());

        if !rrconfig::no_verify() {
            rustc_args.push("-Zalways-encode-mir".to_owned());
            rustc_args.push("-Zpolonius".to_owned());

            if rrconfig::check_overflows() {
                // Some crates might have a `overflow-checks = false` in their `Cargo.toml` to
                // disable integer overflow checks, but we want to override that.
                rustc_args.push("-Coverflow-checks=on".to_owned());
            }

            if rrconfig::dump_debug_info() {
                rustc_args.push(format!(
                    "-Zdump-mir-dir={}",
                    rrconfig::log_dir().join("mir").to_str().expect("failed to configure dump-mir-dir")
                ));
                rustc_args.push("-Zdump-mir=all".to_owned());
                rustc_args.push("-Zdump-mir-graphviz".to_owned());
                rustc_args.push("-Zidentify-regions=yes".to_owned());
            }
            if rrconfig::dump_borrowck_info() {
                rustc_args.push("-Znll-facts=yes".to_string());
                rustc_args.push(format!(
                    "-Znll-facts-dir={}",
                    rrconfig::log_dir()
                        .join("nll-facts")
                        .to_str()
                        .expect("failed to configure nll-facts-dir")
                ));
            }
        }

        let mut callbacks = RRCompilerCalls {};

        rustc_driver::RunCompiler::new(&rustc_args, &mut callbacks).run()
    });

    std::process::exit(exit_code)
}
