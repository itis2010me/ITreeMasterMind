/-! # Game rules (pure: no ITree, no IO)

Rules: 6 colors, codes of length 4, colors may repeat, 10 turns.
A guess is typed as 4 digits 1-6 (one per color), e.g. `1234`.

Everything here is a plain function you can test with `#eval` (and later prove
things about). The game loop in `Game.lean` only calls these.

Exercises:
  1. `inductive Color` with six colors: red, green, blue, yellow, purple, orange.
     Add `deriving DecidableEq, Repr` (`DecidableEq` gives `==` and `count`).
     `abbrev Code := Vector Color codeLength` (define `codeLength` first).
     A `Vector α n` is an `Array α` plus a proof that its size is `n`.
     Literals: `#v[.Red, .Blue, .Red, .Green]` (wrong length = compile error).
  2. `allColors : List Color` (all six), and `codeLength : Nat := 4`, `maxTurns : Nat := 10`.
  3. `Color.ofChar : Char → Option Color` ('1' ↦ first color, ... '6'; anything
     else `none`) and `Color.toChar : Color → Char` (the reverse).
  4. `parseGuess : String → Option Code`
       - turn it into characters (`String.toList`)
       - convert every character with `Color.ofChar`; if any fails, `none`.
         Hint: `List.mapM` in the `Option` monad does exactly this.
       - check the length is `codeLength`, and keep the proof: `if h : ... then`
         names the fact, so you can build `⟨arr, h⟩ : Vector Color codeLength`.
         Hint: check `l.toArray.size = codeLength` (that is exactly the field
         a `Vector` needs), not `l.length`.
  5. `structure Feedback where exact : Nat; near : Nat`
       - exact: right color, right position
       - near:  right color, wrong position
  6. `feedback (secret guess : Code) : Feedback` -- the core of Mastermind.
       - exact: count positions where they agree. `Vector.zip` / `zipWith`
         keep the length; `.toList` gets back to list tools (`filter`, `length`).
       - near: for each color c, `min (secret.count c) (guess.count c)`
         is the number of c's that match *somewhere*; sum that over `allColors`,
         then subtract `exact`.
     Test cases (secret, guess ↦ exact, near):
       1234, 1234 ↦ 4, 0
       1234, 4321 ↦ 0, 4
       1133, 3333 ↦ 2, 0
       1234, 1111 ↦ 1, 0
       1234, 5566 ↦ 0, 0
  7. `showCode : Code → String` and `showFeedback : Feedback → String`
     (e.g. "exact 2, near 1").
-/

namespace Mastermind

abbrev numColors : Nat := 6
inductive Color where
    | White
    | Black
    | Red
    | Yellow
    | Blue
    | Green
deriving DecidableEq, Repr

def codeLength : Nat := 4 -- each guess has to be 4 colors
def maxTurns   : Nat := 10 -- each game can have at most 10 turns

abbrev Code := Vector Color codeLength -- each guess is a vector of 4 colors
def allColors : List Color :=
    [Color.White, Color.Black, Color.Red, Color.Yellow, Color.Blue, Color.Green]

def Color.ofNum : Fin numColors → Color := allColors.get
def Color.toFin : Color → Fin numColors
    | White  => 0
    | Black  => 1
    | Red    => 2
    | Yellow => 3
    | Blue   => 4
    | Green  => 5

abbrev ParseError := String

-- '1'..'6' ↦ the color at index 0..5. `'1' ≤ c` rules out '0' and anything
-- below it, which would otherwise wrap to 0 (Nat subtraction stops at 0).
def Color.ofChar (c : Char) : Except ParseError Color :=
    let n := c.toNat - '1'.toNat
    if h : '1' ≤ c ∧ n < numColors then -- h is the conjunction
        .ok (Color.ofNum ⟨n, h.2⟩) -- Fin needs a proof that n is < numColors
    else
        throw s!"'{c}' is not a color (use 1-{numColors})"

def parseGuess (s : String) : Except ParseError Code := do
    let colors ← s.toList.mapM Color.ofChar
    if h : colors.toArray.size = codeLength then
        return ⟨colors.toArray, h⟩ -- anonymous constuctor for vector
    else
        throw s!"need {codeLength} colors, got {colors.length}"

structure Feedback where
    exact : Nat -- Fin codeLength + 1
    near  : Nat -- Fin codeLength + 1
    -- exact + near := Fin codeLength + 1
deriving Repr, DecidableEq

/-- How many pegs of the guess list can be matched against `rest`, using each
peg of `rest` at most once: a match `erase`s that one peg (first occurrence
only), so it can't be matched again. Structural recursion on the guess list. -/
def nearCount (rest : List Color) : List Color → Nat
    | []      => 0
    | g :: gs =>
        if rest.contains g then
            1 + nearCount (rest.erase g) gs
        else
            nearCount rest gs

/-- Score a guess against the secret, in two passes ("consume" algorithm).
  1. exact: pair the pegs by position; the equal pairs are exact matches.
  2. near:  on the leftover pegs only, match each guess peg against a secret
     peg of the same color, consuming it (`nearCount`), so no secret peg is
     counted twice.

Example, secret `1123`, guess `2111` (digits stand for colors):
```
pairs     [(1,2), (1,1), (2,1), (3,1)]
partition same [(1,1)]                 exact = 1
          diff [(1,2), (2,1), (3,1)]
unzip     secret [1,2,3], guess [2,1,1]
nearCount 2 ∈ [1,2,3] yes, rest [1,3]
          1 ∈ [1,3]   yes, rest [3]
          1 ∈ [3]     no               near  = 2
```
The third `1` finds nothing: the secret's leftover `1` was already used.
Result `⟨1, 2⟩`. -/
def eval (secret guess : Code) : Feedback :=
    let pairs := secret.toList.zip guess.toList
    let (same, diff) := pairs.partition (fun (s, g) => s == g)
    let (restSecret, restGuess) := diff.unzip
    { exact := same.length, near := nearCount restSecret restGuess }

/-- A code as the digits the player types, e.g. `1123` (inverse of `parseGuess`). -/
def showCode (c : Code) : String :=
    String.join (c.toList.map (fun color => toString (color.toFin.val + 1)))

def showFeedback (f : Feedback) : String :=
    s!"exact {f.exact}, near {f.near}"

-- Tests, written as typed input (1 = White ... 6 = Green).
def evalStr (secret guess : String) : Option Feedback :=
    match parseGuess secret, parseGuess guess with
    | .ok s, .ok g => some (eval s g)
    | _, _         => none

#guard evalStr "1234" "1234" == some ⟨4, 0⟩
#guard evalStr "1234" "4321" == some ⟨0, 4⟩
#guard evalStr "1133" "3333" == some ⟨2, 0⟩
#guard evalStr "1234" "1111" == some ⟨1, 0⟩
#guard evalStr "1234" "5566" == some ⟨0, 0⟩
#guard evalStr "1123" "2111" == some ⟨1, 2⟩

-- showCode undoes parseGuess
#guard (match parseGuess "6521" with | .ok c => showCode c | .error e => e) == "6521"
#guard showFeedback ⟨1, 2⟩ == "exact 1, near 2"

end Mastermind
