# student

Lecture code and slides for Functional Programming.

## Setup
- Install VS Code and its Lean 4 extension (publisher `leanprover`); the
  extension walks you through installing Lean itself. For other editors, see
  https://lean-lang.org/install/.
- Your first `lake build` here downloads Mathlib into this repo: about 7.5 GB,
  and again in every other repo you clone. To keep one shared copy instead,
  install https://github.com/jesyspa/lean-global-cache and run `lean-cache
  use` at the repo root before building — the Lake project is in `code/`, and
  a run at the root sweeps it. It also installs a pre-push hook that builds
  first, so you cannot push work that does not compile.
