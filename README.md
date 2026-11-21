# ITreeMasterMind

Learning project: implement the game Mastermind in [Lean 4](https://lean-lang.org/)
using **interaction trees** (ITrees), with a plain command-line interface.

The plan is to build the ITree machinery from scratch in core Lean (no Mathlib,
no dependencies), keep the game logic pure, and interpret game events through
swappable handlers (real stdin/stdout, or scripted input for tests).

References:
- [Interaction Trees: Representing Recursive and Impure Programs in Coq](https://dl.acm.org/doi/pdf/10.1145/3371119) (POPL 2020)
- [boogie-org/lean-itrees](https://github.com/boogie-org/lean-itrees)

## Layout

| Path | Contents |
|---|---|
| `Main.lean` | Entry point of the `itreemastermind` executable |
| `Mastermind/` | The game: ITree library, events, interpreters, pure rules (`Logic.lean`), the game loop |
| `Proofs/` | Theorems about the game: `Logic.lean` (scoring is fully correct, repeats included) and `Parse.lean` (parsing and printing codes are inverses); checked by `lake test` |
| `Practice/Nat.lean` | Practice with inductive types: a custom `Nat'` with `geNat`, `addNat`, and conversions to and from `Nat` |
| `Practice/Theorems.lean` | Theorems about the `Nat'` definitions (proofs in progress; unfinished ones are `sorry`) |

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain version is
pinned in `lean-toolchain`.

Compiling the program and checking the proofs are separate steps:

| Command | What it does |
|---|---|
| `lake build` | Compile the executable (only `Main.lean` and what it imports; proofs are not checked) |
| `lake test` | Check every proof in `Proofs/` (the `Proofs` library is the `testDriver`; building it checks the proofs) |
| `lake build && lake test` | Both |

The `#guard` tests in `Mastermind/Logic.lean` run whenever that module is compiled.

Other commands:

```sh
lake build                      # build the default targets (the executable)
lake build Practice             # build and check the Practice library
lake build Practice.Theorems    # build a single module
lake exe itreemastermind        # build and run the executable
lake env lean Practice/Nat.lean   # check one file directly
lake clean                      # delete build output (.lake/build)
```
