# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A learning project: implement the game Mastermind in Lean 4 using interaction trees (ITrees), with a plain CLI (no TUI). The owner has a Haskell/Brick Mastermind and is learning Lean and ITrees from scratch. The real ITree/game code does not exist yet; `Main.lean` is still the `lake init` hello-world and everything under `Practice/` is staged learning material.

## Commands

```sh
lake build                       # default targets only (the `itreemastermind` exe)
lake build Practice              # build + check all of Practice/ (this is the one to run after edits)
lake build Practice.Tree         # a single module
lake exe itreemastermind         # run the executable
lake env lean Practice/List.lean # check one file directly; #eval output prints to the terminal
```

There is no test framework. "Tests" are `#eval`/`#guard` lines at the bottom of each file; they print during `lake build` only when that module is rebuilt. Pipe a scratch snippet through `lake env lean --stdin` (with `import Practice.X`) to try things without touching the repo.

`defaultTargets` lists only the executable, so plain `lake build` and the GitHub Actions CI (`.github/workflows/lean_action_ci.yml`, runs `lake build`) do **not** check `Practice/`.

## Structure

- `Main.lean`: entry point of the `itreemastermind` exe.
- `Practice/*.lean`: one module per topic, built as the `Practice` `lean_lib` (`globs = ["Practice.+"]`, so new files are picked up with no lakefile change). `Nat.lean` (`Nat'`), `List.lean` (`List'` + `Monad` instance), `Tree.lean` (decision tree with a `Bool → Tree α` field), `Theorems.lean` (statements about `Nat'`; two proved, the rest `sorry` on purpose). `Monads/` holds the monads-from-scratch detour (see PLAN.md): `Option.lean` has `Option'` and `Except' ε` with `Monad` instances; `State.lean` is next.
- No dependencies: core Lean only, no Mathlib. Keep it that way unless the owner asks.

## Design decisions (not derivable from the code)

- ITrees will be an **ordinary inductive type** (`ret | tau (Unit → ITree) | vis (e : E A) (k : A → ITree)`), not a true coinductive. Infinite loops come from `partial def` (which needs an `Inhabited` instance). `bind` is structural and total. This gives up `eutt` and reasoning about infinite traces; that is accepted.
- `lean-itrees` (boogie-org) was evaluated and rejected: it is pinned to Lean v4.12 + Mathlib via QPF cofixpoints, likely not executable, and much of it is `sorry`. It is a reference only.
- The game loop will be bounded by a turn counter so it stays total and provable.
- Game logic stays pure; effects are events (`getLine`, `putLine`, ...) interpreted by swappable handlers (real IO vs scripted input for tests).
- Proofs are deliberately deferred. Do not fill in `sorry`s in `Practice/Theorems.lean` unprompted.

## Working with the owner

- It is a guided-learning session, not a feature build. The owner writes the code; when they say "guide me" or are stuck, give hints and questions, not the finished answer. Show full code only when they ask.
- They edit in VS Code with auto-save, so files change under you. Re-read a file before editing it and before copying line ranges out of it. Do not `git checkout` a file to restore it without checking for their uncommitted edits.
- `PLAN.md` (gitignored, local only) holds the 8-step curriculum, with each exercise tied to the ITree piece it prepares. Steps 1-2 (List/Monad) are done; step 3 (`Tree.lean`) is in progress; step 4 is an answer-indexed event type `Cmd : Type → Type`.
- Commits and pushes happen only when asked. Remote: `github.com/itis2010me/ITreeMasterMind`, branch `main`.

## Lean 4.35 gotchas seen here

- `#eval` derives `Repr` automatically, so `deriving Repr` is unnecessary for printing. `=` in `#eval` needs `DecidableEq` (derived on `List'`).
- `String.trim` does not exist; use `trimAscii.toString`.
- `open Nat'` does not carry across `import`; re-open it in each file.
- Bare constructor names in patterns need `open` or a leading dot; otherwise they become fresh pattern variables.
