import Practice.Cmd

/-! # `Free E R`: an ITree without `tau`
Step 6 of PLAN.md.

    Free E R = ret (r : R)                         -- finished with result r
             | vis (e : E A) (k : A → Free E R)    -- ask for e, continue with its answer

Pieces you already have:
  * `Tree`  (step 3): a node holding a continuation `Bool → Tree α`.
    `vis` is the same, but the question is any `e : E A` and the answer type is `A`.
  * `Cmd`   (step 4): our `E`. `vis Cmd.getLine k` needs `k : String → Free Cmd R`.
  * `State'`/`Except'` (monads): `bind` that builds a new continuation.
  * `scripted`/`handleIO` (step 4): handle ONE event. Here you run a whole program.

Exercises:
  1. Define `inductive Free (E : Type → Type) (R : Type)` with `ret` and `vis`.
     `vis` mentions a type `A` that is not a parameter of `Free`: make it an
     implicit argument of the constructor, `{A : Type} → E A → (A → Free E R) → Free E R`.
     Then `#check Free`. Why is the result `Type 1` and not `Type`?
  2. Write by hand (no `do`) a program `hello : Free Cmd Unit` that prints
     "What is your name?", reads a line, and prints a greeting.
     Compare its shape with `t2` in `Tree.lean`.
  3. `bind : Free E α → (α → Free E β) → Free E β`.
       - `ret a`: what do you do with `a`?
       - `vis e k`: you cannot call `f` yet (no `α` available). Keep `e`, and
         build a NEW continuation that first runs `k` and then binds with `f`.
     Then `instance : Monad (Free E)`.
  4. `trigger (e : E A) : Free E A`: a program that does just `e` and returns its answer.
     Rewrite `hello` with `do` and `trigger`.
  5. Two interpreters for `Free Cmd α`:
       - `runScripted : Free Cmd α → List String → α × List String`, using `scripted`
       - `runIO : Free Cmd α → IO α`, using `handleIO`
     Same program, two meanings. Call `runIO` from `Main.lean` instead of
     calling `handleIO` line by line.
  6. Questions to answer in a comment:
       - Why does `bind` on `vis` not need to know anything about `E`?
       - `runScripted` recurses on `k x`, not on a direct subterm. Why does Lean
         still accept it as structural recursion? (Compare `depth` in `Tree.lean`.)
       - What could a program NOT do yet, that a real game loop needs? (Hint: step 7.)

Tests: `#eval` lines at the bottom (`runScripted` can be `#eval`ed; `runIO` cannot
read input under `#eval`).
-/

inductive Free (E : Type → Type) (R : Type) where
    | ret : R → Free E R
    | vis : {A : Type} → E A → (A → Free E R) → Free E R

-- binder style, same as above
-- inductive Free' (E : Type → Type) (R : Type) where
--     | ret (R : Type)
--     | vis {A : Type} (e : E A) (k : A → Free E R)

#check Free

def freeHello : Free Cmd Unit :=
    Free.vis (Cmd.putLine "Hello") (fun _ =>
        Free.vis (Cmd.getLine) (fun name =>
            Free.vis (Cmd.putLine s!"Hello {name}") (fun _ =>
                Free.ret ())))

/-
`freeBind m f`: run program `m`, then continue with `f` on its result.
  * `ret r`   : `m` is finished, so hand over to `f r`.
  * `vis e k` : `m` is stuck on request `e` (no answer yet, so `f` can't run).
                Keep `e`; wrap the continuation so that, once an interpreter
                supplies the answer `x`, it runs the rest of `m` (`k x`) and
                then `f`.
The recursive call sits under `fun x =>`, so it unfolds one level per answer,
until it reaches a `ret`. Net effect: `f` is grafted onto every `ret` of `m`.
`bind` never looks inside `e`; only interpreters give requests a meaning.
`x : A✝`, the answer type of `e` (`✝` = the implicit `A` we didn't name).
-/
def freeBind : Free E α → (α → Free E β) → Free E β
    | Free.ret r,   f => f r
    | Free.vis e k, f => Free.vis e (fun x => freeBind (k x) f)

-- pure : {α : Type} -> α -> m α
def freePure {α : Type} {E : Type → Type} (a : α) : Free E α := Free.ret a

instance : Monad (Free E) where
    pure := freePure
    bind := freeBind


def trigger {E : Type → Type} {A : Type} (e : E A) : Free E A :=
    Free.vis e (fun x => Free.ret x)

/-
  vis (putLine "Hello") (fun _ =>
    vis getLine (fun name =>
      vis (putLine s!"Hello {name}") (fun y =>
        ret y)))
-/
def freeHello' : Free Cmd Unit := do
    trigger (Cmd.putLine "Hello, what is your name?")
    let name ← trigger Cmd.getLine
    trigger (Cmd.putLine s!"Hello {name}")


def runIO : Free Cmd α → IO α
    | Free.ret a => pure a
    | Free.vis e k => do
        let x ← handleIO e
        runIO (k x)
