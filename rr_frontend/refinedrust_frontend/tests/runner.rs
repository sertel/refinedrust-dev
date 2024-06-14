use std::{env, path, process};

const TARGET_DIR: &str = if cfg!(debug_assertions) { "debug" } else { "release" };

fn build_refinedrust() {
    let mut cargo = process::Command::new("cargo");
    cargo.arg("build");

    let status = cargo.status().expect("failed to build refinedrust project");
    assert!(status.success());
}

fn build_subproject(project_path: &str) {
    let Ok(crate_dir) = env::var("CARGO_MANIFEST_DIR") else {
        panic!("CARGO_MANIFEST_DIR must be set to find the home of the crate");
    };

    let Some(workspace_dir) = path::Path::new(&crate_dir).parent() else {
        unreachable!("The crate `refinedrust_frontend` is inside a workspace");
    };

    let target_dir = workspace_dir.join("target").join(TARGET_DIR);
    let path = format!("{}:{}", target_dir.display(), env::var("PATH").unwrap_or_default());

    let mut cargo = process::Command::new("cargo");
    cargo.env("PATH", path);
    cargo.args(["-Z", "unstable-options"]).args(["-C", project_path]);
    cargo.arg("refinedrust");

    let status = cargo.status().expect(project_path);
    assert!(status.success());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn run_deps_build() {
        build_refinedrust();
        build_subproject("./tests/deps_build/");
    }
}
