/-! # Game events and their handlers
Copied from `Practice/Cmd.lean` (step 4). The game uses this copy; the Practice
file stays as the learning record.

TODO (yours):
  * `handleIO` `getLine`: trim the trailing newline (`trimAscii.toString`),
    otherwise `"y\n" == "y"` is false and `"42\n".toNat?` is `none`.
  * `handleIO` `randInt n`: drop `IO.setRandSeed n` and use `n` as the bound,
    so `randInt n` gives a number in `0 .. n`.
-/

namespace Mastermind

inductive Cmd : Type → Type where
    | getLine : Cmd String
    | putLine : String → Cmd Unit
    | randInt : Nat → Cmd Nat

def describe : Cmd α → String
    | Cmd.getLine   => "Read a line"
    | Cmd.putLine s => s!"Print {s}"
    | Cmd.randInt n => s!"Random int {n}"

def scripted : Cmd α → List String → α × List String
    | Cmd.getLine, []         => ("", [])
    | Cmd.getLine, x :: xs    => (x, xs)
    | Cmd.putLine _, inputs   => ((), inputs)
    | Cmd.randInt n, inputs   => (n, inputs)

def handleIO : Cmd α → IO α
    | Cmd.getLine => do
        let stdin ← IO.getStdin
        let line ← stdin.getLine
        return line.trimAscii.toString
    | Cmd.putLine s => IO.println s
    | Cmd.randInt n => IO.rand 0 n

end Mastermind
