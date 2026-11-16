/-! # Monads from scratch
Monads detour in PLAN.md, Phase 2.

Lesson 1: `Option'` and `Except' ε`.

Exercises:
  1. Define `inductive Option' (α : Type)` with `none'` and `some'`.
  2. Write `pure` and `bind` as plain functions first, then wrap them in
     `instance : Monad Option'`. (Look at your `Monad List'` instance in
     `Practice/List.lean` for the shape.)
  3. Use it: `safeDiv : Nat → Nat → Option' Nat`, then a `do` block that
     chains three divisions and short-circuits when one divisor is zero.
  4. Define `inductive Except' (ε α : Type)` with `error'` and `ok'`.
     Note `ε` is fixed, so the instance is `Monad (Except' ε)`.
  5. Redo `safeDiv` as `Except' String Nat`, with an error message, and check
     that the first failure's message is the one you get back.
  6. Questions to answer in a comment:
       - What does `bind` do on `none'` / `error' e`?
       - Why is `Option'` the same as `Except' Unit`, up to renaming?

Tests: `#eval` lines at the bottom.
-/

inductive Option' (α : Type) where
   | none' : Option' α
   | some' : α → Option' α

-- binder style, above is the arrow style, both produce the same constructor
-- inductive Option' (α : Type) where
--    | none
--    | some (val : α)

-- monad's pure instance has type pure : {α : Type} -> α -> m α
def optionPure {α : Type} (val : α) : Option' α := Option'.some' val

def optionBind {α β : Type} (m : Option' α) (f : α -> Option' β) : Option' β :=
   match m with
   | Option'.none' => Option'.none'
   | Option'.some' a => f a

instance : Monad Option' where
   pure := optionPure
   bind := optionBind

def safeDiv (x y : Nat) : Option' Nat :=
   match y with
   | 0 => Option'.none'
   | _ => Option'.some' (x / y)

#eval do
   let x <- safeDiv 5 1
   let y <- safeDiv 4 0
   return (x,y) -- return none'

inductive Except' (ε α : Type) where
   | error' : ε -> Except' ε α
   | ok' : α -> Except' ε α

def exceptPure {ε α : Type} (val : α) : Except' ε α := Except'.ok' val
def exceptBind {α β ε : Type} (m : Except' ε α) (f : α -> Except' ε β) : Except' ε β :=
   match m with
   | Except'.error' exp => Except'.error' exp
   | Except'.ok' a => f a

-- monad wants m : Type -> Type, not Type → Type → Type
-- since the Exception message or whatever depend on another type, we need to pin, or
-- make Except' take in the Type already to make its type Type -> Type, such as Except' String
instance {ε : Type} : Monad (Except' ε) where
   pure := exceptPure
   bind := exceptBind

def exceptionMsgDiv (x y : Nat) : Except' String Nat :=
   match y with
   | 0 => Except'.error' "Division by zero!"
   | _ => Except'.ok' (x / y)

def exceptionGeneralMsgDiv (x y : Nat) : Except' String Nat :=
   match y with
   | 0 => Except'.error' "Arithmetic Error!"
   | _ => Except'.ok' (x / y)

#eval do
   let x <- exceptionMsgDiv 5 0
   let y <- exceptionGeneralMsgDiv 4 0
   return (x,y) -- Except'.error' "Division by zero"

#eval do
   let x <- exceptionMsgDiv 5 1
   let y <- exceptionGeneralMsgDiv 4 0
   return (x,y) -- Except'.error' "Arithmetic Error!"

/-
Questions to answer in a comment:
   - What does `bind` do on `none'` / `error' e`?
      bind for none'(Option') will stop the further chaining of f and just return none'
      bind for error' e(Except') will stop further chaining and return the error message or object
      in both case the f is NEVER called
   - Why is `Option'` the same as `Except' Unit`, up to renaming?
      Unit is (), which is exactly one value. The renaming is renaming .error' () to .none'
-/


