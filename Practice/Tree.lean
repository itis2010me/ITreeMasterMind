/-! # Tree with a function-typed field
Step 3 of PLAN.md.

ITree link: `vis e k` has a continuation `k : A → ITree`. The child is a
*function*, not a stored subtree. Here the simplest version of that idea:
a `node` asks a yes/no question and holds one subtree per possible answer,
as a function `Bool → Tree α`.

To write next:
  * a function that walks a tree by being given a list of answers
  * `depth`-like questions: why can't we just recurse on "the children"?
-/

/-
A decision tree ("twenty questions"): each `node` asks a yes/no question and
each `leaf` is a final result.

  * `leaf a`  : finished with result `a`.            (ITree: `ret`)
  * `node k`  : ask a question; `k true` is the "yes" subtree, `k false` the
                "no" subtree.                        (ITree: `vis`, with the
                question fixed and the answer type fixed to `Bool`)

Unlike an ordinary binary tree, the children are NOT stored. They are computed
by the function `k` when you supply an answer, so you can only look at a
subtree by calling `k true` or `k false`. Using a function (instead of two
fields) also scales: `Fin 6 → Tree α` gives 6 children, `Nat → Tree α` gives
infinitely many, which is what `vis` needs for arbitrary answer types.
-/
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : (Bool → Tree α) → Tree α

open Tree

def t1 : Tree Nat :=
  node (fun q => if q then (leaf 1) else (leaf 2))

def f : Bool := True

def t2 : Tree String :=
  node (fun q => if q then (leaf "A") else
    node (fun q2 => if q2 then (leaf "B") else (leaf "C")))


def run : Tree α -> List Bool -> Option α
  | leaf a, List.cons _ _ => some a
  | node f, List.cons x xs => run (f x) xs
  | leaf a, [] => some a
  | node _, [] => none

#eval run t1 [true] == some 1
#eval run t1 [true, false] == some 1
#eval run t2 [false, true] == some "B"


-- depth function for the depth of the decision tree
-- one decision is 1 level
def depth : Tree α -> Nat
  | leaf _ => 0
  | node f => (max (depth (f true)) (depth (f false))) + 1

#eval depth t1
#eval depth t2
