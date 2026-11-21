import Mastermind.Run

/-! # Drills: `Cmd`, `trigger`, `ITree`
Small, repetitive exercises to make the three ideas automatic before the game.
Uses the real `Mastermind` library (do NOT also import `Practice.Cmd` here:
both define a `Cmd`).

The four ideas being drilled:
  * `Cmd A`         : a request whose answer is an `A` (just data, does nothing)
  * `trigger e`     : a one-request program that returns the answer
  * `ITree Cmd R`   : a whole program, built with `do` (= `bind`)
  * `runIO` / other : interpreters; the only place a request gets a meaning

## A. Read and predict (no code; write answers in comments)
  A1. For each, give its type: `Cmd.getLine`, `trigger Cmd.getLine`,
      `Cmd.putLine "x"`, `trigger (Cmd.putLine "x")`, `Cmd.randInt 5`.
  A2. Which of these are valid lines in a `do` block of type `ITree Cmd Unit`,
      and why?  `Cmd.getLine`  /  `let s ← trigger Cmd.getLine`  /
      `let s := Cmd.getLine`  /  `trigger (Cmd.putLine "hi")`  /  `IO.println "hi"`
  A3. How many `vis` nodes does a run of `drillGreetTwice` (B1) go through?
      Does that number depend on the input?
  A4. For `drillYesNo` (B2): draw the tree down to the `ret`s, with one branch
      for "y" and one for "anything else".

## B. Write small programs (each one: run it from `Main.lean` with `runIO`)
  B1. `drillGreetTwice : ITree Cmd Unit`: ask a name, greet; ask again, greet again.
  B2. `drillYesNo : ITree Cmd Bool`: ask "continue? (y/n)", return `true` on "y".
  B3. `drillSum : ITree Cmd Unit`: read two lines, print their sum
      (`toNat?`; on bad input print an error, no retry yet).
  B4. `drillEcho : Nat → ITree Cmd Unit`: echo `n` lines back, by recursion on `n`.
  B5. `drillCountUntilQuit : ITree Cmd Nat` with `iter` (state = the count).
  B6. `drillAskNat : ITree Cmd Nat` with `iter`: ask until the line parses.
      Then redo B3 using it, so bad input retries.
  B7. Reuse: `drillMenu : ITree Cmd Unit`: show "1) sum 2) echo 3) quit", read a
      choice, run B3 / B4 / stop; loop with `iter` until "3".

## C. By hand vs `do`
  C1. Write B1 with only `ITree.vis` / `ITree.ret` (no `do`, no `trigger`).
  C2. Desugar B2's `do` block into `ITree.bind` calls, then into the final tree.

## D. Interpreters (programs are data)
  D1. `runScripted : ITree Cmd α → List String → α × List String`
      (`ret`, `tau`, `vis` cases; use `scripted` from `Mastermind/Cmd.lean`).
      `#eval` B1..B4 with fixed input lists. Careful with `iter` programs:
      `scripted` answers "" when the inputs run out, so B6 with no valid line
      would loop forever. Always give it input that ends the loop.
  D2. `trace : ITree Cmd α → List String → List String`: like `runScripted` but
      return the list of `describe e` for every request made, in order.
      `#eval trace drillGreetTwice ["Ada", "Bob"]` and read the program's "log".
  D3. Same program, three interpreters (IO, scripted, trace): what changed?
      What did NOT change?
-/

namespace Mastermind

end Mastermind
