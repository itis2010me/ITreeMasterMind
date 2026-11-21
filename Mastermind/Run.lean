import Mastermind.ITree
import Mastermind.Cmd

/-! # Interpreters: give `ITree Cmd` programs a meaning

Exercises:
  1. `runIO : ITree Cmd α → IO α`: your `Free` `runIO` plus a `tau` case
     (nothing to do: just run `t ()`).
  2. Optional: `runScripted : ITree Cmd α → List String → α × List String`
     using `scripted`, for `#eval` tests of the game with fixed input.
     A scripted loop that never gets valid input would run forever; that is
     the price of `iter`.
  3. Test program: `askNat : ITree Cmd Nat` that keeps asking until the line
     parses with `String.toNat?`, written with `iter`. Run it from `Main.lean`
     and try a few bad inputs first.
-/

namespace Mastermind
def runIO : ITree Cmd α → IO α
    | ITree.ret a => pure a
    | ITree.tau t => runIO (t ())
    | ITree.vis e k => do
        let x ← handleIO e
        runIO (k x)

end Mastermind
