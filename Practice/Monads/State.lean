/-! # State monad from scratch
Monads detour in PLAN.md, Phase 2. Lesson 2.

First monad that is a *function*, not data: `State' σ α := σ → α × σ`.
A computation takes the current state and returns a result plus the new state.

Exercises:
  1. Define `State' (σ α : Type) : Type` as the function type above.
  2. `pure'` : give a value without touching the state.
  3. `bind'` : write it as `fun s => ...`. Follow the types:
       `m s` gives a pair; `f` wants the result; the next step needs the *new* state.
  4. `instance : Monad (State' σ)`. If `do` blocks later fail with
     "failed to synthesize Monad", try `abbrev` instead of `def`.
  5. Primitives (not part of `Monad`): `get'`, `set'`, `modify'`.
  6. `run' (m : State' σ α) (s : σ) : α × σ`, just applying `m` to `s`.
  7. Test with a `do` block, start state 5:
       let s ← get'
       set' (s * 2)
       let y ← get'
       return y
     Predict the result (should be `(10, 10)`). Then break `bind'` on purpose
     (pass the old state to `f`) and see which test notices.
  8. A counter: `tick : State' Nat Nat` returns the current count and adds 1.
     Use it three times in one `do` block to label items.
  9. Questions to answer in a comment:
       - What does `pure'` do to the state?
       - In `bind'`, why can't you call `f` before running `m`?
       - Why is `State' σ` (not `State'`) the thing that is a monad?

Tests: `#eval` lines at the bottom.
-/

-- σ - type of the state, α - type of the result
-- Type -> Type -> Type
-- σ    -> α    -> σ → α × σ
def State' (σ α : Type) : Type := σ → α × σ

-- pure : {α : Type} -> α -> m α
def statePure {σ α : Type} (a : α) : State' σ α :=
   fun state => (a, state)

-- bind
/-
  1. take in the initial state s
  2. run m on s to get a pair (a, s')   -- a : α is the result, s' : σ is the new state
  3. apply f to the result a only       -- f a : State' σ β is the next machine
  4. run f a on the new state s'        -- the pair it returns (b, s'') is the answer: result b, final state s''
-/
def stateBind {σ α β : Type} (m : State' σ α) (f : α -> State' σ β) : State' σ β :=
   fun s =>
      let (r', s') := m s
      let s2 := f r'
      s2 s'

instance {σ : Type} : Monad (State' σ) where
   pure := statePure
   bind := stateBind

-- State primitives other than pure and bind
-- get'
def get' {σ : Type} : State' σ σ :=
   fun s => (s, s)
-- set - set the state to input x
def set' {σ : Type} (x : σ) : State' σ Unit :=
   fun _ => ((), x)

-- modify - modify the state based on given function g
def modify' {σ : Type} (g : σ → σ) : State' σ Unit :=
   fun s => ((), g s)

-- run
def run' {σ α : Type} (m : State' σ α) (s : σ) : α × σ := m s


def test : State' Nat Nat := do
   let s ← get'
   set' (s * 2)
   let y ← get'
   return y

#eval test 5 -- (10, 10)

def tick : State' Nat Nat := fun s => (s, s + 1)

def label3 : State' Nat (List Nat) := do
   let a ← tick
   let b ← tick
   let c ← tick
   return [a, b, c]


/-
- What does `pure'` do to the state?
   It takes in a value and return a function that is waiting for a state, the function
   returns a pair (result, input state)
- In `bind'`, why can't you call `f` before running `m`?
   We need to get the result in order to call f, since the type of f is f : α -> State' σ β
   Running the initial monad m with the input state will get us the pair, which then can apply f to result
   to get the new state monad back
- Why is `State' σ` (not `State'`) the thing that is a monad?
   monad is Type -> Type, State is Type -> Type -> Type
-/
