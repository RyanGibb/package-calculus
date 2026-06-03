This artifact accompanies the paper *Package Managers à la Carte: A Formal Model of Dependency Resolution*.
It should be evaluated against the revised version of the paper, which differs from the conditionally-accepted version.

This artifact is a Lean 4 mechanisation of the Package Calculus: a core calculus of dependency resolution, a family of extensions modelling features found in real-world package managers, a composition of two of those extensions, and the NP-completeness of dependency resolution (via a 3SAT reduction).
For a mapping of paper definitions and theorems see the ./paper-mapping.md file.

This is a proof-script artifact; there is no executable tool to run: the contribution is the machine-checked development itself.

## Requirements

- The Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.28.0`).
  This is installed automatically by [`elan`](https://github.com/leanprover/elan), and bundles the build tool `lake`.
- Mathlib, pinned to the revision in `lakefile.toml` and locked in `lake-manifest.json`.

The artifact has been tested on Linux.
The Lean toolchain also runs on macOS and Windows, so the build is expected to work there too.
These dependencies are pre-installed in the VM image.

## VM build

From the project root:

```sh
make build    # build the whole development
make validate # build, then print the axioms behind every headline theorem
```

`make validate` executes scripts/axioms.lean to audit axioms.
A clean audit lists, for each headline theorem, only Lean's standard classical axioms -- `propext`, `Classical.choice`, and `Quot.sound`.

`make clean` drops only this development's `.olean`s, so `make build` recompiles just it against the cached Mathlib -- fast and offline.

## Source build

Install Lean via `elan` (its version manager) following the official instructions (<https://lean-lang.org/install/manual/>) with `curl https://elan.lean-lang.org/elan-init.sh -sSf | sh`, or via your operating system's package manager.
`elan` provides the `lake` build tool and installs the pinned toolchain automatically.
Then, from the project root:

```sh
make cache
make build
make validate
```

`make cache` fetches Mathlib's cached `.olean` files matching the pinned revision; without it, Mathlib is compiled from source, which can take a long time.
