/-! # Interaction trees
Step 7 of PLAN.md: `Free` (step 6) plus `tau`, plus a loop combinator `iter`.

    ITree E R = ret (r : R)
              | tau (t : Unit → ITree E R)            -- one silent step
              | vis (e : E A) (k : A → ITree E R)

Why `tau`: a loop that goes around again without asking anything still has to
produce *some* node; `tau` is that "nothing visible happened, keep going" step.
Why `Unit → ...` (a thunk): the rest of the loop must not be built until someone
runs it. A function body is only evaluated when the function is called, so the
recursive call inside `fun () => ...` stays unevaluated until then.

Exercises (most are your `Free` code again, plus one `tau` case):
  1. `inductive ITree (E : Type → Type) (R : Type)` with `ret`, `tau`, `vis`.
  2. `ITree.bind`. The `tau t` case: like `vis`, you can't call `f` yet; keep the
     `tau` and bind the rest (`t ()`) inside a new thunk.
  3. `instance : Monad (ITree E)` and `trigger (e : E A) : ITree E A`.
  4. `instance [Inhabited R] : Inhabited (ITree E R)`, e.g. `⟨ret default⟩`.
     `partial def` (next exercise) needs its result type to be `Inhabited`.
  5. `partial def iter (body : α → ITree E (α ⊕ β)) (a : α) : ITree E β`
     (add `[Inhabited β]`). Run `body a`; on `.inl a'` go around again behind a
     `tau`, on `.inr b` finish with `b`.
       - `α ⊕ β` is `Sum α β`: `.inl` = "continue with this", `.inr` = "done with this".
       - Why `partial`? Lean cannot prove the loop ends. What does `partial` give up?
  6. Questions to answer in a comment:
       - What would go wrong if `tau` held an `ITree E R` directly instead of a thunk?
       - Why does `bind` still not need to know anything about `E`?

Interpreters go in `Mastermind/Run.lean`.
-/

namespace Mastermind

inductive ITree (E : Type → Type) (R : Type) where
    | ret : R → ITree E R
    | tau : (Unit → ITree E R) → ITree E R
    | vis : {A : Type} → E A → (A → ITree E R) → ITree E R

def ITree.bind : ITree E α → (α → ITree E β) → ITree E β
    | ITree.ret r,   f => f r
    | ITree.tau t,   f => ITree.tau (fun () => bind (t ()) f)
    | ITree.vis e k, f => ITree.vis e (fun x => bind (k x) f)

-- pure : {α : Type} -> α -> m α
def ITree.pure {α : Type} {E : Type → Type} (a : α) : ITree E α := ITree.ret a

instance : Monad (ITree E) where
    pure := ITree.pure
    bind := ITree.bind

def trigger {E : Type → Type} {A : Type} (e : E A) : ITree E A :=
    ITree.vis e (fun x => ITree.ret x)

instance [Inhabited R] : Inhabited (ITree E R) := ⟨ITree.ret default⟩

/-
`iter body a`: a loop. `body` is one iteration; it takes the loop state and
returns a program whose result says what to do next:
  * `.inl a'` : go around again with new state `a'` (behind a `tau`)
  * `.inr b`  : stop; the whole loop returns `b`
The recursive call sits inside the `tau` thunk, so the next iteration is only
built when an interpreter runs that `tau`. Without the thunk, `iter` would try
to build every iteration up front and never finish.
`partial`: Lean can't prove the loop ends, so it skips the termination check and
treats `iter` as opaque in proofs (needs `Inhabited (ITree E β)`, hence `[Inhabited β]`).
-/
partial def iter [Inhabited β] (body : α → ITree E (α ⊕ β)) (a : α) : ITree E β :=
    ITree.bind (body a) (fun r =>
        match r with
        | .inl a' => ITree.tau (fun () => iter body a')
        | .inr b  => ITree.ret b)

end Mastermind
