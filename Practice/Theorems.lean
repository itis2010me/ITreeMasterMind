import Practice.Inductive
open Nat'

/-! Theorems about `Nat'`, `addNat`, `toOrdNat`, `toNat'` and `geNat`.
    Each proof is `sorry` for now: replace it, one at a time. -/

/-! ## addNat: basic equations -/

theorem addNat_zero_left (n : Nat') : addNat zero n = n := by
  rfl

theorem addNat_zero_right (n : Nat') : addNat n zero = n := by
  induction n with
  | zero => rfl
  | succ x ih =>
    show succ (addNat x zero) = succ x
    rw [ih]

theorem addNat_succ_left (n : Nat') : ∀ m : Nat', addNat (succ m) n = succ (addNat m n) := by
  sorry

theorem addNat_succ_right (m n : Nat') : addNat m (succ n) = succ (addNat m n) := by
  sorry

/-! ## addNat: algebraic laws -/

theorem addNat_assoc (a b c : Nat') : addNat (addNat a b) c = addNat a (addNat b c) := by
  sorry

theorem addNat_comm (a b : Nat') : addNat a b = addNat b a := by
  sorry

/-! ## Conversions to and from `Nat` -/

theorem toOrdNat_addNat (a b : Nat') : toOrdNat (addNat a b) = toOrdNat a + toOrdNat b := by
  sorry

theorem toOrdNat_toNat' (n : Nat) : toOrdNat (toNat' n) = n := by
  sorry

theorem toNat'_toOrdNat (n : Nat') : toNat' (toOrdNat n) = n := by
  sorry

/-! ## geNat -/

theorem geNat_refl (n : Nat') : geNat n n = true := by
  sorry

theorem geNat_zero_right (n : Nat') : geNat n zero = true := by
  sorry
