
## Editor configuration for working on the frontend
To work on the frontend and get nice autocompletion for rustc internal things, etc., you can use `rust-analyzer`.
The `Cargo.toml` for `rr_frontend` sets the right flags to make `rust-analyzer` use rustc-internal things.

The remaining config depends on your editor.

### Vim
For Vim, [`YouCompleteMe`](https://github.com/ycm-core/YouCompleteMe) has good support for Rust using `rust-analyzer`.
Look at its README for instructions on configuring keybinds.

However, by default, it ships its own `rustc` toolchain and sources which are used for completion and which are not updated frequently
(this is apparently due to `rust-analyzer` having a very unstable API; see https://github.com/ycm-core/YouCompleteMe/issues/4012).
This creates problems, because YCM will constantly rebuild the project with its own toolchain (and the build cache will conflict with `cargo build` in the `refinedrust` toolchain, so it needs to do full rebuilds),
and you won't get proper autocompletion of `rustc` internals.

The `_vimrc_local.vim` file shipped in this project already mostly takes care of setting the right toolchain (if you have installed `https://github.com/LucHermitte/local_vimrc`), by setting:
```
let g:ycm_rust_toolchain_root = '/home/[user]/.rustup/toolchains/refinedrust'
```
You just have to change the `[user]` to match your setup (sadly, references to `home` by `~/` or `$HOME/` do not seem to be supported).

To set the `rustc` sources, setup a `.ycm_extra_conf.py` file (for setting it globally, add e.g.
```
let g:ycm_global_ycm_extra_conf = "~/.vim/.ycm_extra_conf.py"
```
to your `.vimrc`) and put the following into it:
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

TODO: can we also point directly to the `rust-src` in the `refinedrust` toolchain? Problem: it does not have `Cargo.toml`.


## Updating the frontend's rustc version
1. Update the file `rust-version` in `rr_frontend` to the new desired `rust-lang/rust` commit.
2. Run `./rustup_toolchain` in `rr_frontend`.
3. Try to get the frontend building again.


