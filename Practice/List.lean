/-! # List'
Step 1 of PLAN.md. A type with a parameter, like `ITree E R`.
Functions to write inside the namespace below:
  length', append, map, flatMap (`flatMap` is `bind` for lists)
-/

/-
Universe levels: `Nat : Type`, but `Type : Type 1`, `Type 1 : Type 2`, ...
(a type can't contain itself). `Type u` means "a type at some level `u`":
`List' Nat` uses u = 0, `List' Type` uses u = 1. Lean infers `u` for us.
-/
inductive List' (α : Type u) where
  | nil  : List' α
  | cons : α → List' α → List' α
deriving Repr, DecidableEq

namespace List'
def length : List' α -> Nat
  | nil => 0
  | cons _ xs => 1 + length xs

#eval length (cons 1 (cons 2 (cons 3 nil)))
#eval length (cons True (cons False (cons True nil)))
#eval length (nil : List' Type)
#eval length (cons Nat (cons String (cons Bool nil))) -- list of Types, at level 0
#eval length (cons Type nil) -- List of Type type, at Type 1
#eval length (cons (Nat -> Nat) nil) -- function are also in Type 0

def append : List' α -> List' α -> List' α
  -- | t, nil => t
  | nil, t => t
  | cons x xs, t => cons x (append xs t)

#eval append (cons 1 (cons 2 nil)) (cons 3 nil)
#eval append (cons 1 (cons 2 nil)) nil

def push : List' α -> α -> List' α
  | nil, t => cons t nil
  | cons x xs, t => cons x (push xs t)

#eval push (cons 1 (cons 2 nil)) 3
#eval push (cons 1 (cons 2 nil)) 0

def push' (l: List' α) (a : α) : List' α :=
  append l (cons a nil)

-- needs DecidableEq
#eval (push (cons 1 (cons 2 nil)) 3) = (push' (cons 1 (cons 2 nil)) 3)

-- Arguments before the `:` are named and in scope in every case (`f` below).
-- Arguments after the `:` are only part of the type, so pattern matching
-- (`|`) needs one slot per argument. Put what you match on after the colon,
-- and what you merely use (like `f`) before it. Both forms are the same function.
def map (f : α -> β) : List' α -> List' β
  | nil => nil
  | cons x xs => cons (f x) (map f xs)

-- `(· + 1)` is shorthand for `fun x => x + 1`; each `·` is an argument slot.
-- Type `·` in VS Code as `\.` then Space/Tab.
#eval map (· + 1) (cons 1 (cons 2 nil)) = cons 2 (cons 3 nil)
#eval map (· * 2) (nil : List' Nat) = nil
-- element type changes: Nat -> String
#eval map toString (cons 1 (cons 2 nil)) = cons "1" (cons "2" nil)
-- map distributes over append
#eval map (· + 1) (append (cons 1 nil) (cons 2 nil))
    = append (map (· + 1) (cons 1 nil)) (map (· + 1) (cons 2 nil))


def flatMap (f : α → List' β) : List' α → List' β
  | nil => nil
  | cons x xs => append (f x) (flatMap f xs)

#eval flatMap (fun x => cons x (cons x nil)) (cons 1 (cons 2 nil))
    = cons 1 (cons 1 (cons 2 (cons 2 nil)))                      -- duplicates
#eval flatMap (fun x => if x > 1 then cons x nil else nil) (cons 1 (cons 2 (cons 3 nil)))
    = cons 2 (cons 3 nil)                                        -- filters
#eval flatMap (fun x => cons x nil) (cons 1 (cons 2 nil))
    = cons 1 (cons 2 nil)                                        -- a function that wraps each element

-- similar to pure
def singleton (x : α) : List' α :=
  cons x nil

#eval flatMap singleton (cons 1 (cons 2 (cons 3 nil))) = cons 1 (cons 2 (cons 3 nil))

end List'

-- preparation for making List' into a monad

instance : Monad List' where
  pure      := List'.singleton
  bind xs f := List'.flatMap f xs

open List'

-- `:=` just names a value: x and y are the whole lists. No `bind` is called,
-- so this is only two `let`s and an expression. Result: [1, 2, 10, 20].
#eval (do
  let x := cons 1 (cons 2 nil)
  let y := cons 10 (cons 20 nil)
  append x y)

-- `←` calls `bind`: x is ONE element of the list at a time (a Nat, not a list),
-- and the rest of the block runs once per element. Each `←` is a nested `bind`:
--   bind xs (fun x => bind ys (fun y => pure (x + y)))
-- Result: every (x, y) combination, summed: [11, 21, 12, 22].
#eval (do
  let x ← cons 1 (cons 2 nil)
  let y ← cons 10 (cons 20 nil)
  pure (x + y) : List' Nat) = cons 11 (cons 21 (cons 12 (cons 22 nil)))
