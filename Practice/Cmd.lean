/-! # Answer-indexed events: `Cmd : Type → Type`
Step 4 of PLAN.md.

ITree link: in `vis (e : E A) (k : A → ITree E R)`, the event `e : E A` carries
the type `A` of its own answer, and the continuation `k` must accept exactly an `A`.
`E` is a type-level function `Type → Type`; `Cmd` is our `E`.

Exercises:
  1. Define `inductive Cmd : Type → Type` with
       `getLine : Cmd String`
       `putLine : String → Cmd Unit`
     Note: the `Type` goes AFTER the colon (an index, not a parameter).
     Use arrow style so each constructor can state its own result type.
  2. Questions to answer in a comment:
       - Why can't `Cmd` be `inductive Cmd (α : Type)` with these constructors?
       - What is the type of `Cmd.getLine`? Of `Cmd.putLine "hi"`?
  3. Write `describe : Cmd α → String` ("read a line" / "print: ...")
     by matching on the constructor.
  4. Write a *handler by hand*: `scripted : Cmd α → List String → α × List String`
     which for `getLine` pops the next scripted line (or "" if none) and for
     `putLine _` returns `()` and leaves the list alone.
     Hint: the result type `α` changes per constructor, so check that Lean
     accepts the match, and notice what the match tells it about `α`.
  5. Add one more event, e.g. `randInt : Nat → Cmd Nat` (or `getSecret : Cmd Code`
     later), and see what you have to change.
  6. Real handler: `handleIO : Cmd α → IO α` using Lean's own IO
     (`IO.getStdin` + `.getLine`, `IO.println`, `IO.rand`). Compare its type with
     `scripted : Cmd α → List String → α × List String` (= `State' (List String) α`).
     Try it from `Main.lean` (`lake exe itreemastermind`), since `#eval` cannot
     wait for keyboard input.

Tests: `#eval` lines at the bottom.
-/

inductive Cmd : Type → Type where
   | getLine : Cmd String
   | putLine : String → Cmd Unit
   | randInt : Nat -> Cmd Nat

/-
Exercise 2:
  - Why can't `Cmd` be `inductive Cmd (α : Type)` with these constructors?
      A parameter (before the colon) is fixed for the whole type, so every
      constructor would have to return the same `Cmd α`. Here `getLine` returns
      `Cmd String` and `putLine` returns `Cmd Unit`: each constructor picks its own
      result type, which needs an index (after the colon). The index is the type of
      the request's *answer*, not something stored inside it.
  - What is the type of `Cmd.getLine`? Of `Cmd.putLine "hi"`?
      `Cmd.getLine : Cmd String` and `Cmd.putLine "hi" : Cmd Unit`.
-/
#check Cmd                 -- Cmd : Type → Type
#check Cmd.getLine         -- Cmd String
#check Cmd.putLine "hi"    -- Cmd Unit

-- take in a Cmd α and returns a string describing what that command does
def describe : Cmd α → String
   | Cmd.getLine => "Read a line"
   | Cmd.putLine s => s!"Print {s}"
   | Cmd.randInt n => s!"Random int {n}"


def scripted : Cmd α -> List String -> α × List String
   | Cmd.getLine, [] => ("", [])
   | Cmd.getLine, x::xs => (x, xs)
   | Cmd.putLine _, scripts => ((), scripts)
   | Cmd.randInt n, scripted => (n, scripted)

#eval scripted Cmd.getLine ["line1", "line2"]
#eval scripted Cmd.getLine []
#eval scripted (Cmd.putLine "line") ["line1", "line2"]


def handleIO : Cmd α → IO α
   | Cmd.getLine => do
      let stdin ← IO.getStdin
      let line ← stdin.getLine
      return line
   | Cmd.putLine s => IO.println s
   | Cmd.randInt n => do
      IO.setRandSeed n -- seeded with input n
      let num ← IO.rand 0 1000 -- random number between 0 and 1000
      return num
