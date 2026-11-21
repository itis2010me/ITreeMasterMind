import Mastermind.Logic
import Mastermind.Run

/-! # The game, as an `ITree Cmd` program

Exercises (after `Logic.lean`):
  1. `randomCode : ITree Cmd Code`: four random colors.
       - `trigger (Cmd.randInt 5)` gives an index 0..5; pick from `allColors`
         (`allColors[i]!`, or `getD i Color.red`).
       - four times: write it out, or recurse on a `Nat` counter.
  2. `askGuess : ITree Cmd Code`: prompt, read, `parseGuess`; on `none` print
     an error and ask again. Use `iter` (state `()`), like `echoUntilQuit`.
  3. `inductive Result | won (turns : Nat) | lost (secret : Code)`.
  4. `loop (secret : Code) : Nat → Nat → ITree Cmd Result`, arguments
     `turnsLeft` and `turn`, by structural recursion on `turnsLeft`:
       - `0`: lost.
       - `n + 1`: ask a guess, compute and print feedback; if exact = codeLength
         then won, else `loop secret n (turn + 1)`.
  5. `game : ITree Cmd Result`: intro text, `randomCode`, `loop secret maxTurns 1`,
     print the outcome, return the result.
  6. `Main.lean`: `runIO game`.
-/

namespace Mastermind

end Mastermind
