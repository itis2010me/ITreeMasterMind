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
| `Practice/Inductive.lean` | Practice with inductive types: a custom `Nat'` with `geNat`, `addNat`, and conversions to and from `Nat` |
| `Practice/Theorems.lean` | Theorems about the `Nat'` definitions (proofs in progress; unfinished ones are `sorry`) |

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain version is
pinned in `lean-toolchain`.

```sh
lake build                      # build the default targets (the executable)
lake build Practice             # build and check the Practice library
lake build Practice.Theorems    # build a single module
lake exe itreemastermind        # build and run the executable
lake env lean Practice/Inductive.lean   # check one file directly
lake clean                      # delete build output (.lake/build)
```
