import Proofs.Logic

/-! # Theorems about parsing and printing codes
`parseGuess` and `showCode` are inverses:
  * `parseGuess_showCode` : printing then parsing gives back the code
  * `showCode_parseGuess` : anything that parses is exactly what `showCode` prints
Together: the valid inputs are exactly the 4-digit strings over 1-6, one per code.
-/

namespace Mastermind

/-- The digit a color is typed as (spec for the helpers below; not used by the game). -/
def Color.digit : Color → Char
    | White  => '1'
    | Black  => '2'
    | Red    => '3'
    | Yellow => '4'
    | Blue   => '5'
    | Green  => '6'

/-- `showCode` prints each color as its digit (6 cases, checked by `decide`). -/
theorem Color.toString_digit (c : Color) : (toString (c.toFin.val + 1)).toList = [c.digit] := by
    cases c <;> decide

/-- Guards: typing a color's digit gives that color. -/
theorem Color.ofChar_digit (c : Color) : Color.ofChar c.digit = .ok c := by
    cases c <;> rfl

theorem Color.digit_toNat (c : Color) : c.digit.toNat = '1'.toNat + c.toFin.val := by
    cases c <;> rfl

/-- Guards: `ofChar` accepts only the six digits; anything it accepts is the
digit of the color it returns (so '0', '7', ' ' etc. are all rejected). -/
theorem Color.ofChar_ok (ch : Char) (c : Color) (h : Color.ofChar ch = .ok c) : ch = c.digit := by
    unfold Color.ofChar at h
    dsimp only at h
    split at h
    · rename_i hc
      injection h with h
      subst h
      apply Char.toNat_inj.mp
      have h1 := Color.digit_toNat (Color.ofNum ⟨ch.toNat - '1'.toNat, hc.2⟩)
      rw [Color.toFin_ofNum] at h1
      dsimp only at h1
      have h2 : '1'.toNat ≤ ch.toNat := Fin.mk_le_mk.mp hc.1
      omega
    · cases h

/-- `showCode` is just the digits of the colors, in order. -/
theorem showCode_toList (c : Code) : (showCode c).toList = c.toList.map Color.digit := by
    simp only [showCode, String.toList_join, List.flatMap_map, Color.toString_digit]
    generalize c.toList = l
    induction l <;> simp_all

/-- Parsing a list of digits gives back the colors. -/
theorem mapM_ofChar_digit (l : List Color) : (l.map Color.digit).mapM Color.ofChar = .ok l := by
    induction l with
    | nil => rfl
    | cons c l ih => simp [List.mapM_cons, Color.ofChar_digit, ih]; rfl

/-- If every character parsed, the characters were exactly those digits. -/
theorem mapM_ofChar_ok (l : List Char) (cs : List Color) (h : l.mapM Color.ofChar = .ok cs) :
        l = cs.map Color.digit := by
    induction l generalizing cs with
    | nil => cases h; rfl
    | cons ch l ih =>
        rw [List.mapM_cons] at h
        cases hc : Color.ofChar ch with
        | error e => simp [hc] at h; cases h
        | ok c =>
            cases hl : l.mapM Color.ofChar with
            | error e => simp [hc, hl] at h; cases h
            | ok cs' =>
                simp [hc, hl] at h
                change Except.ok (c :: cs') = Except.ok cs at h
                injection h with h
                subst h
                rw [Color.ofChar_ok ch c hc, ih cs' hl]
                rfl

/-! ## The round trips -/

/-- Guards: every code the game prints can be typed back in and parses to the
same code (e.g. the revealed secret, or a code echoed in a message). -/
theorem parseGuess_showCode (c : Code) : parseGuess (showCode c) = .ok c := by
    unfold parseGuess
    rw [showCode_toList, mapM_ofChar_digit]
    have hs : c.toList.toArray.size = codeLength := by simp
    simp only [bind, Except.bind]
    simp only [hs, ↓reduceDIte]
    congr

/-- Guards: `parseGuess` accepts only the strings `showCode` would print, so
exactly 4 digits 1-6 and nothing else (no spaces, extra or missing pegs). -/
theorem showCode_parseGuess (s : String) (c : Code) (h : parseGuess s = .ok c) :
        showCode c = s := by
    unfold parseGuess at h
    cases hm : s.toList.mapM Color.ofChar with
    | error e => simp [hm, bind, Except.bind] at h
    | ok colors =>
        simp only [hm, bind, Except.bind] at h
        split at h
        · rename_i hs
          injection h with h
          subst h
          apply String.ext
          rw [showCode_toList, mapM_ofChar_ok s.toList colors hm]
          simp
        · cases h

end Mastermind
