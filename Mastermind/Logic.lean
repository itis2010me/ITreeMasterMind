/-! # Game rules (pure: no ITree, no IO)

Rules: 6 colors, codes of length 4, colors may repeat, 10 turns.
A guess is typed as 4 letters, e.g. `rgby`.

Everything here is a plain function you can test with `#eval` (and later prove
things about). The game loop in `Game.lean` only calls these.

Exercises:
  1. `inductive Color` with six colors: red, green, blue, yellow, purple, orange.
     Add `deriving DecidableEq, Repr` (`DecidableEq` gives `==` and `List.count`).
     `abbrev Code := List Color`.
  2. `allColors : List Color` (all six), and `codeLength : Nat := 4`, `maxTurns : Nat := 10`.
  3. `Color.ofChar : Char → Option Color` ('r' ↦ red, ...; anything else `none`)
     and `Color.toChar : Color → Char` (the reverse).
  4. `parseGuess : String → Option Code`
       - lowercase it (`String.toLower`), turn it into characters (`String.toList`)
       - convert every character with `Color.ofChar`; if any fails, `none`.
         Hint: `List.mapM` in the `Option` monad does exactly this.
       - check the length is `codeLength`.
  5. `structure Feedback where exact : Nat; near : Nat`
       - exact: right color, right position
       - near:  right color, wrong position
  6. `feedback (secret guess : Code) : Feedback` -- the core of Mastermind.
       - exact: count positions where they agree (`List.zip`, then `filter`, `length`).
       - near: for each color c, `min (count c in secret) (count c in guess)`
         is the number of c's that match *somewhere*; sum that over `allColors`,
         then subtract `exact`.
     Test cases (secret, guess ↦ exact, near):
       rgby, rgby ↦ 4, 0
       rgby, ybgr ↦ 0, 4
       rrgg, gggg ↦ 2, 0
       rgby, rrrr ↦ 1, 0
       rgby, oopp ↦ 0, 0
  7. `showCode : Code → String` and `showFeedback : Feedback → String`
     (e.g. "exact 2, near 1").
-/

namespace Mastermind

end Mastermind
