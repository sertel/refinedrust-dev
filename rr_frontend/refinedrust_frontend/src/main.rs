// This file uses code from the Prusti project (function `mir_borrowck`) under the MPL 2.0 license, https://github.com/viperproject/prusti-dev/blob/master/prusti/src/callbacks.rs.
//
// This file uses code adapted from the miri project (function `run_compiler`) under the MIT license, https://github.com/rust-lang/miri/blob/master/src/bin/miri.rs
//
// Other parts of the source are © 2023, The RefinedRust Developers and Contributors
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.



#![feature(box_patterns)]
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_span;
extern crate rustc_trait_selection;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_session;
extern crate rustc_attr;
extern crate rustc_target;
extern crate rustc_type_ir;
extern crate polonius_engine;

use log::{debug, info};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::query::{queries::mir_borrowck, Providers, ExternProviders};
use std::env;

use rustc_driver::Compilation;
use rustc_interface::Config;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;

use std::process::Command;

use translation::environment::mir_storage;
use translation;

/// Args for the compiler.
pub const REFINEDRUST_DEFAULT_ARGS: &[&str] = &[
    // have debug assertions in the generated code
    "-Cdebug-assertions=on",
    // TODO: make this a config option
    "-Coverflow-checks=on",
    // use Polonius
    "-Zpolonius",
];

/// Callbacks for the RefinedRust frontend.
struct RRCompilerCalls {
}

// From Prusti.
fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> mir_borrowck::ProvidedValue<'tcx> {
    let body_with_facts = rustc_borrowck::consumers::get_body_with_borrowck_facts(
        tcx,
        def_id,
        rustc_borrowck::consumers::ConsumerOptions::PoloniusOutputFacts
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
pub fn analyze<'tcx>(tcx : TyCtxt<'tcx>) {
    // TODO Also think about putting different modules into different Coq files.
    translation::generate_coq_code(tcx, |vcx| vcx.write_coq_files());


    if let Some(true) = rrconfig::check_proofs() {
        if cfg!(target_os = "windows") {
            println!("Cannot run proof checker on Windows.");
        }
        else {
            let dir_str = rrconfig::output_dir();
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
    fn config(&mut self, config : &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(override_queries);
    }

    fn after_analysis<'tcx>(
        &mut self,
        _handler: &rustc_session::EarlyErrorHandler,
        _ : &rustc_interface::interface::Compiler,
        queries : &'tcx rustc_interface::Queries<'tcx>
    ) -> Compilation {
            // Analyze the crate and inspect the types under the cursor.
            queries.global_ctxt().unwrap().enter(|tcx| {
                analyze(tcx);
            }
        );
        Compilation::Stop
    }
}




/// Execute a compiler with the given CLI arguments and callbacks.
/// (adapted from Miri)
fn run_compiler(
    mut args: Vec<String>,
    callbacks: &mut (dyn rustc_driver::Callbacks + Send),
    insert_default_args: bool,
) -> ! {
    if insert_default_args {
        // Some options have different defaults in Miri than in plain rustc; apply those by making
        // them the first arguments after the binary name (but later arguments can overwrite them).
        args.splice(1..1, REFINEDRUST_DEFAULT_ARGS.iter().map(ToString::to_string));
    }

    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&args, callbacks).run()
    });
    std::process::exit(exit_code)
}

fn main() {
    rustc_driver::install_ice_hook("", |_| ());

    env_logger::init();

    println!("\
______      __ _                _______          _    \n\
| ___ \\    / _(_)              | | ___ \\        | |   \n\
| |_/ /___| |_ _ _ __   ___  __| | |_/ /   _ ___| |_  \n\
|    // _ \\  _| | '_ \\ / _ \\/ _` |    / | | / __| __| \n\
| |\\ \\  __/ | | | | | |  __/ (_| | |\\ \\ |_| \\__ \\ |_  \n\
\\_| \\_\\___|_| |_|_| |_|\\___|\\__,_\\_| \\_\\__,_|___/\\__| \n\
");
    //TODO possibly hook into the rrconfig for cmd args

    let mut rustc_args = vec![];

    for arg in env::args() {
        if rustc_args.is_empty() {
            // Very first arg: binary name.
            rustc_args.push(arg);
        } else {
            match arg.as_str() {
                _ => {
                    // Forward to rustc.
                    rustc_args.push(arg);
                }
            }
        }
    }

    // always compile as a lib, so that we don't need a main function
    rustc_args.push("--crate-type=lib".to_string());

    debug!("rustc arguments: {:?}", rustc_args);


    run_compiler(
        rustc_args,
        &mut RRCompilerCalls { },
        true,
    );

}
