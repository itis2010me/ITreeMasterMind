inductive Nat' where
  | zero : Nat'
  | succ : Nat' -> Nat'

-- Add both zero and succ into the current namespace
open Nat'

-- given 2 Nat', this is the >= operator
def geNat : Nat' -> Nat' -> Bool
  | zero, zero => true
  | succ _, zero => true
  | zero, succ _ => false
  | succ x, succ y => geNat x y

#eval geNat zero zero
#eval geNat zero (succ zero)
#eval geNat (succ zero) zero
#eval geNat (succ zero) (succ zero)
#eval geNat (succ zero) (succ (succ zero))
#eval geNat (succ (succ zero)) (succ zero)

-- add two Nat'
def addNat : Nat' -> Nat' -> Nat'
  -- | zero, zero => zero
  -- | zero, succ x => succ x
  | zero, t => t
  -- | succ x, zero => succ x
  -- | succ x, succ y => succ (succ (addNat x y))
  | succ x, t => succ (addNat x t)

#eval addNat zero zero
#eval addNat zero (succ zero)
#eval addNat (succ zero) zero
#eval addNat (succ zero) (succ zero)
#eval addNat (succ zero) (succ (succ zero))
#eval addNat (succ (succ zero)) (succ zero)

def toOrdNat : Nat' -> Nat
  | zero => 0
  | succ x => 1 + toOrdNat x -- toOrdNat x + 1 is the more idomatic syntax

#eval toOrdNat zero = 0
#eval toOrdNat (succ (succ (succ zero))) = 3
#eval toOrdNat (addNat (succ (succ zero)) (succ zero)) = 3

def toNat' : Nat -> Nat'
  | 0 => zero
  | x + 1 => succ (toNat' x)

#eval toOrdNat (toNat' 5) = 5
#eval toOrdNat (toNat' 0) = 0
