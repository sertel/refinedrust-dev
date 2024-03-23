# Information for RefinedRust developers

## Setup
You will need to install some specific dependencies in order to have a development setup of this project.

There are two maintained ways to do this, using `nix` or (`opam` and `rustup`).

Both methods require you to have a local copy of this project.

### Setup using `nix` flakes
We assume that you have `nix` installed on your system. Setup instructions can be found here: https://nixos.org/download

To setup the project for development purposes, you can use `nix develop` to enter an interactive subshell containing the tools you will need:
```bash
cd <refinedrust-root-project>
make setup-nix
nix develop
```

The tools lives in this subshell and will disappear as soon as you leave the subshell.

If you do not have flakes enabled, you may get this error:
```
error: experimental Nix feature 'nix-command' is disabled; use ''–extra-experimental-features nix-command' to override
```

All you have to do is enable flakes, see this [NixOS wiki page](https://nixos.wiki/wiki/Flakes) for more details on how to enable flakes permanently.

Note: Make sure that you are not currently in an opam switch with a Coq installation -- this may confuse our build setup.

### Setup using `opam` and `rustup`
By following the procedure in the `README.md`, you should have the required setup for development.

## Editor configuration for working on the frontend
To work comfortably on the frontend, it is recommended to use `rust-analyzer`, which provides nice features to your editor like code completion.

If you are using `nix develop`, the following command must be run each time the toolchain is updated due [to a bug inside `cargo`](https://github.com/rust-lang/cargo/issues/10096):
```bash
sudo unshare -m bash -c "mount -o remount,rw /nix/store; cargo metadata --format-version 1 --manifest-path ${RUST_SRC_PATH}"
```

Furthermore, it is required that `rust-analyzer.rustc.source` points to the value of `${RUST_SRC_PATH}`:
```bash
echo ${RUST_SRC_PATH}  # Keep this path, you will need it.
```

The remaining configuration depends on your editor.

### Emacs
For Emacs, you need to install the [LSP Mode plugin](https://emacs-lsp.github.io/lsp-mode/page/installation/).

After installation, you need to configure the property `rust-analyzer.rust.source` to point out the location of the source of `rust-analyzer` (`RUST_SRC_PATH`).

This property has to be set in your configuration, and can be temporarily set by using:
```
<M-x> set-variable, choose `lsp-rust-analyzer-rustc-source` and replace by "<the path given by ${RUST_SRC_PATH}>"
<M-x> lsp-restart-workspace
```

Please remember to update this value each time the rust toolchain is updated.

### Vim
For Vim, [`YouCompleteMe`](https://github.com/ycm-core/YouCompleteMe) has good support for Rust using `rust-analyzer`.
Look at its README for instructions on configuring keybinds.

However, by default, it ships its own `rustc` toolchain and sources which are used for completion and which are not updated frequently.
This creates problems, because YCM will constantly rebuild the project with its own toolchain (and the build cache will conflict with `cargo build` in the toolchain RefinedRust uses, so it needs to do full rebuilds),
and you won't get proper autocompletion of `rustc` internals.

You can fix this by setting by giving the path to the current toolchain explicitly.
First, get the output of `rustc --print sysroot` and copy it.
Then, put the following into your vim configuration (if you have a plugin for local configuration like `https://github.com/LucHermitte/local_vimrc`, we recommend putting this into the configuration for this project):
```
let g:ycm_rust_toolchain_root = '[SYSROOT]'
```
where `SYSROOT` is the output of `rustc --print sysroot`.

To set the `rustc` sources, setup a `.ycm_extra_conf.py` file (for setting it globally, add e.g.
```
let g:ycm_global_ycm_extra_conf = "~/.vim/.ycm_extra_conf.py"
```
to your `.vimrc`) and put the following into it, putting the right path to a checkout of https://github.com/rust-lang/rust):
```
def Settings(**kwargs):
  if kwargs['language'] == 'rust':
    return {
      'ls': {
        "rustcSource" : "/home/[...]/rust-git/Cargo.toml",
      }
    }
```
(if you already set other options, add just the `rustcSource` config).

### Visual Studio Code
For Visual Studio Code, you need to install the [rust-analyzer extension](https://marketplace.visualstudio.com/items?itemName=rust-lang.rust-analyzer).

After installation, you need to configure the property `rust-analyzer.rust.source` to point out the location of the source of `rust-analyzer` (`RUST_SRC_PATH`).

This property has to be set inside the `settings.json` file of your user (not the workspace):
```json
{
    "rust-analyzer.rustc.source": "<the path given by ${RUST_SRC_PATH}>"
}
```

Please remember to update this value each time the rust toolchain is updated, by repeating the same steps.

## Updating dependencies

### Updating the frontend's rustc version
1. Update the file `rust-toolchain.toml` to the new desired nightly version.
2. Make the required changes for `nix` (see below).
3. Try to get the frontend building again.

### Updating `nix` dependencies
The project is described with `nix` using the file `flake.nix`, containing a list of `inputs` and `outputs`.

#### Updating `nix` inputs
The `inputs` set contains some repositories (`fenix`, `nixpkgs`, ...) that describe how to build dependencies.

In order to be reproducible, this `inputs` set is locked to a specific version
using the file `flake.lock`.

To update this set, you can use `nix flake update` and commit the modified `flake.lock` file.

#### Updating `nix` outputs
The `outputs` set describe the project, including how to build some external dependencies.

Those dependencies are described using a couple:
 - `version`/`sha256` for `coq`, such as `stdpp`, `iris` or `lambda-rust`, and;
 - `dir`/`sha256` for specifying the `rust` toolchain.

To update a dependency:
1. Replace the `sha256` string with the empty string `""`.
2. For a `coq` dependency, replace the `version` string with the desired `git` commit hash.
3. Run `nix build` and wait for the error that throws the hash mismatch.
4. Replace the `sha256` empty string with the hash from the received error.
