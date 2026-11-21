import Mastermind.Logic

/-! # Theorems about the game rules
Proofs about `Logic.lean`, kept separate so the game only imports the code.
Several come from the Haskell QuickCheck properties (CSE230MM `Ptest.hs`):
there they were checked on 10000 random inputs, here they hold for all inputs.

  1. `Color.ofNum_toFin`  / 2. `Color.toFin_ofNum` : the color numbering round-trips
  3. `nearCount_le`       : near never exceeds the leftover guess pegs
  4. `eval_le`            : at most 4 pins            (prop_judgeSize)
  5. `eval_self`          : the secret scores 4 exact
  6. `eval_exact_spec`    : exact = the obvious spec  (prop_redJudge)
  7. `eval_no_RRRW`       : never 3 exact + 1 near    (prop_genSlotInvalid)
  8. `nearCount_nodup`    : no repeats ⇒ consuming changes nothing (prop_whiteJudge)
  9. `eval_nodup_two_le`  : no repeats ⇒ at least 2 pins (prop_genSlotEmpty / Empty1)
 10. `nearCount_eq_matchTotal` : consume = counting (min of counts per color)
 11. `eval_total`         : exact + near = sum over colors of min counts.
                            With #6 this fully specifies `eval`, repeats included.
-/

namespace Mastermind

/-! ## Helper lemmas -/

/-- `eval`'s `exact`, with the `partition` replaced by a plain `filter`. -/
theorem eval_exact (secret guess : Code) :
        (eval secret guess).exact =
            ((secret.toList.zip guess.toList).filter (fun p => p.1 == p.2)).length := by
    simp [eval, List.partition_eq_filter_filter]

/-- `eval`'s `near`, with the `partition`/`unzip` replaced by `filter`/`map`. -/
theorem eval_near (secret guess : Code) :
        (eval secret guess).near =
            let diff := (secret.toList.zip guess.toList).filter (fun p => !(p.1 == p.2))
            nearCount (diff.map Prod.fst) (diff.map Prod.snd) := by
    simp [eval, List.partition_eq_filter_filter]
    rfl

/-- Filtering by `p` and by `not p` splits a list: the two lengths add up. -/
theorem length_filter_add_not (p : α → Bool) (l : List α) :
        (l.filter p).length + (l.filter (fun a => !p a)).length = l.length := by
    induction l with
    | nil => rfl
    | cons a l ih => cases h : p a <;> simp [h] <;> omega

theorem zip_self_eq (l : List Color) : ∀ p ∈ l.zip l, p.1 = p.2 := by
    induction l with
    | nil => simp
    | cons a l ih =>
        intro p hp
        simp at hp
        rcases hp with rfl | hp
        · rfl
        · exact ih p hp

theorem Color.mem_allColors (c : Color) : c ∈ allColors := by
    cases c <;> simp [allColors]

/-! ## Color numbering -/

/-- Guards: `ofNum` and `toFin` use the same numbering, so a color printed as a
digit and typed back in is the same color. -/
theorem Color.ofNum_toFin (c : Color) : Color.ofNum c.toFin = c := by
    cases c <;> rfl

/-- Guards: the other direction; every digit 1-6 names a different color. -/
theorem Color.toFin_ofNum (i : Fin numColors) : (Color.ofNum i).toFin = i := by
    revert i
    decide

/-! ## Scoring -/

/-- Guards: consuming never invents matches; each guess peg gives at most one. -/
theorem nearCount_le (rest gs : List Color) : nearCount rest gs ≤ gs.length := by
    induction gs generalizing rest with
    | nil => simp [nearCount]
    | cons g gs ih =>
        simp only [nearCount, List.length_cons]
        split
        · have := ih (rest.erase g); omega
        · have := ih rest; omega

/-- Guards: never more than 4 pins; no peg is counted twice.
(Haskell `prop_judgeSize`.) -/
theorem eval_le (secret guess : Code) :
        (eval secret guess).exact + (eval secret guess).near ≤ codeLength := by
    rw [eval_exact, eval_near]
    simp only
    have h1 := nearCount_le
        (((secret.toList.zip guess.toList).filter (fun p => !(p.1 == p.2))).map Prod.fst)
        (((secret.toList.zip guess.toList).filter (fun p => !(p.1 == p.2))).map Prod.snd)
    have h2 := length_filter_add_not (fun p : Color × Color => p.1 == p.2)
        (secret.toList.zip guess.toList)
    have h4 : (secret.toList.zip guess.toList).length = codeLength := by simp
    simp only [List.length_map] at h1
    omega

/-- Guards: guessing the secret wins: 4 exact, 0 near. -/
theorem eval_self (s : Code) : eval s s = ⟨codeLength, 0⟩ := by
    have hall : ∀ p ∈ s.toList.zip s.toList, (p.1 == p.2) = true := by
        intro p hp; simp [zip_self_eq _ p hp]
    have h1 : (s.toList.zip s.toList).filter (fun p => p.1 == p.2) = s.toList.zip s.toList :=
        List.filter_eq_self.mpr hall
    have h2 : (s.toList.zip s.toList).filter (fun p => !(p.1 == p.2)) = [] :=
        List.filter_eq_nil_iff.mpr (by intro p hp; simp [hall p hp])
    have he := eval_exact s s
    have hn := eval_near s s
    rw [h1] at he
    simp only [h2] at hn
    cases h : eval s s
    simp_all [nearCount]

/-- Specification of `exact`: count equal positions, one step at a time
(the Haskell `compareM`). Deliberately the most obvious definition. -/
def exactSpec : List Color → List Color → Nat
    | s :: ss, g :: gs => (if s = g then 1 else 0) + exactSpec ss gs
    | _, _             => 0

theorem exact_filter_spec (l₁ l₂ : List Color) :
        ((l₁.zip l₂).filter (fun p => p.1 == p.2)).length = exactSpec l₁ l₂ := by
    induction l₁ generalizing l₂ with
    | nil => simp [exactSpec]
    | cons a l₁ ih =>
        cases l₂ with
        | nil => simp [exactSpec]
        | cons b l₂ =>
            by_cases h : a = b
            · simp [exactSpec, h, ih]; omega
            · simp [exactSpec, h, ih]

/-- Guards: the `zip`/`partition` implementation of exact agrees with the
obvious position-by-position count. (Haskell `prop_redJudge`.) -/
theorem eval_exact_spec (secret guess : Code) :
        (eval secret guess).exact = exactSpec secret.toList guess.toList := by
    rw [eval_exact, exact_filter_spec]

/-- Guards: the impossible result 3 exact + 1 near never appears. The one
leftover pair has different colors, so it can't match itself.
(Haskell `prop_genSlotInvalid`.) -/
theorem eval_no_RRRW (secret guess : Code) :
        (eval secret guess).exact = 3 → (eval secret guess).near = 0 := by
    intro h3
    rw [eval_exact] at h3
    rw [eval_near]
    have hlen := length_filter_add_not (fun p : Color × Color => p.1 == p.2)
        (secret.toList.zip guess.toList)
    have h4 : (secret.toList.zip guess.toList).length = 4 := by
        rw [List.length_zip, Vector.length_toList, Vector.length_toList]; rfl
    have h1 : ((secret.toList.zip guess.toList).filter (fun p => !(p.1 == p.2))).length = 1 := by
        omega
    obtain ⟨⟨a, b⟩, hd⟩ := List.length_eq_one_iff.mp h1
    have hab : a ≠ b := by
        have hm : (a, b) ∈ (secret.toList.zip guess.toList).filter (fun p => !(p.1 == p.2)) := by
            rw [hd]; simp
        simp at hm
        exact hm.2
    simp only [hd]
    simp [nearCount, Ne.symm hab]

/-! ## Codes without repeated colors -/

/-- Guards: with no repeated colors, consuming (`erase`) changes nothing: near is
just "how many leftover secret pegs appear in the leftover guess".
(Haskell `prop_whiteJudge`.) -/
theorem nearCount_nodup (rest gs : List Color) (hr : rest.Nodup) (hg : gs.Nodup) :
        nearCount rest gs = (rest.filter (fun c => gs.contains c)).length := by
    induction gs generalizing rest with
    | nil =>
        rw [List.filter_eq_nil_iff.mpr (by simp)]
        rfl
    | cons g gs ih =>
        have hg' : gs.Nodup := (List.nodup_cons.mp hg).2
        simp only [nearCount]
        split
        · rename_i hc
          have hmem : g ∈ rest := by simpa using hc
          rw [ih (rest.erase g) (hr.erase g) hg']
          -- move `g` to the front of `rest`; it is the one extra match
          have hp := (List.perm_cons_erase hmem).filter (fun c => (g :: gs).contains c)
          rw [hp.length_eq]
          have hne : g ∉ rest.erase g := hr.not_mem_erase
          have hcongr : (rest.erase g).filter (fun c => (g :: gs).contains c)
                  = (rest.erase g).filter (fun c => gs.contains c) := by
              apply List.filter_congr
              intro x hx
              have : x ≠ g := fun h => hne (h ▸ hx)
              simp [this]
          rw [List.filter_cons_of_pos (by simp), List.length_cons, hcongr]
          omega
        · rename_i hc
          have hmem : g ∉ rest := by simpa using hc
          rw [ih rest hr hg']
          congr 1
          apply List.filter_congr
          intro x hx
          have : x ≠ g := fun h => hmem (h ▸ hx)
          simp [this]

/-- Guards: two codes without repeats always get at least 2 pins. Pigeonhole:
4 + 4 colors chosen from 6 must share at least 2, and every shared color is
either an exact or a near match. (Haskell `prop_genSlotEmpty` / `Empty1`.) -/
theorem eval_nodup_two_le (secret guess : Code)
        (hs : secret.toList.Nodup) (hg : guess.toList.Nodup) :
        2 ≤ (eval secret guess).exact + (eval secret guess).near := by
    -- names for the pieces of `eval`
    let s := secret.toList
    let g := guess.toList
    let pairs := s.zip g
    let same := pairs.filter (fun p => p.1 == p.2)
    let diff := pairs.filter (fun p => !(p.1 == p.2))
    let dS := diff.map Prod.fst
    let dG := diff.map Prod.snd
    have hlen : s.length = 4 := by
        show secret.toList.length = 4; rw [Vector.length_toList]; rfl
    have hglen : g.length = 4 := by
        show guess.toList.length = 4; rw [Vector.length_toList]; rfl
    have hfst : pairs.map Prod.fst = s := List.map_fst_zip (by omega)
    have hsnd : pairs.map Prod.snd = g := List.map_snd_zip (by omega)
    -- exact + near in terms of the pieces
    have hE : (eval secret guess).exact = same.length := eval_exact secret guess
    have hdS : dS.Nodup := by
        have : dS.Sublist s := by rw [← hfst]; exact List.filter_sublist.map _
        exact hs.sublist this
    have hdG : dG.Nodup := by
        have : dG.Sublist g := by rw [← hsnd]; exact List.filter_sublist.map _
        exact hg.sublist this
    have hN : (eval secret guess).near = (dS.filter (fun c => dG.contains c)).length := by
        rw [eval_near]
        exact nearCount_nodup dS dG hdS hdG
    -- every color in both codes is an exact match or a near match
    have hsub : s.filter (fun c => g.contains c)
            ⊆ same.map Prod.fst ++ dS.filter (fun c => dG.contains c) := by
        intro x hx
        simp only [List.mem_filter, List.contains_iff_mem] at hx
        obtain ⟨hxs, hxg⟩ := hx
        rw [← hfst] at hxs
        rw [← hsnd] at hxg
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hxs
        obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hxg
        by_cases hP : p.1 = p.2
        · exact List.mem_append_left _ (List.mem_map.mpr ⟨p, by simp [same, hp, hP], rfl⟩)
        · by_cases hQ : q.1 = q.2
          · exact List.mem_append_left _
                (List.mem_map.mpr ⟨q, by simp [same, hq, hQ], by rw [hQ]; exact hqx⟩)
          · apply List.mem_append_right
            simp only [List.mem_filter, List.contains_iff_mem]
            refine ⟨List.mem_map.mpr ⟨p, by simp [diff, hp, hP], rfl⟩, ?_⟩
            exact List.mem_map.mpr ⟨q, by simp [diff, hq, hQ], hqx⟩
    have hle : (s.filter (fun c => g.contains c)).length
            ≤ same.length + (dS.filter (fun c => dG.contains c)).length := by
        have := List.Nodup.length_le_of_subset (hs.sublist List.filter_sublist) hsub
        simpa using this
    -- pigeonhole: g plus the colors of s not in g are all different, so at most 6
    have hpig : (g ++ s.filter (fun c => !g.contains c)).length ≤ allColors.length := by
        apply List.Nodup.length_le_of_subset
        · rw [List.nodup_append]
          refine ⟨hg, hs.sublist List.filter_sublist, ?_⟩
          intro a ha b hb hab
          subst hab
          simp [ha] at hb
        · intro c _
          exact Color.mem_allColors c
    have hsplit := length_filter_add_not (fun c => g.contains c) s
    simp only [List.length_append] at hpig
    have h6 : allColors.length = 6 := rfl
    omega

/-! ## Full correctness, repeated colors included
Helpers first, then `nearCount_eq_matchTotal` and `eval_total`. -/

/-- Total matches ignoring position: for each color, the smaller of its two counts. -/
def matchTotal (r gs : List Color) : Nat :=
    (allColors.map (fun c => min (r.count c) (gs.count c))).sum

theorem sum_map_add (L : List Color) (f h : Color → Nat) :
        (L.map (fun c => f c + h c)).sum = (L.map f).sum + (L.map h).sum := by
    induction L with
    | nil => rfl
    | cons a L ih => simp [ih]; omega

/-- Each color appears exactly once in `allColors`. -/
theorem sum_indicator (g : Color) :
        (allColors.map (fun c => if (g == c) = true then 1 else 0)).sum = 1 := by
    cases g <;> decide

/-- Summing the count of every color gives the length. -/
theorem sum_count (l : List Color) : (allColors.map (fun c => l.count c)).sum = l.length := by
    induction l with
    | nil => simp [allColors]
    | cons a l ih =>
        simp only [List.count_cons, List.length_cons]
        rw [sum_map_add, ih, sum_indicator]

theorem matchTotal_nil (r : List Color) : matchTotal r [] = 0 := by
    simp [matchTotal, allColors]

/-- Guards: the consume algorithm (`nearCount`) computes exactly the standard
count-based total, repeats included. Your Haskell `judgeW`/`check` = counting. -/
theorem nearCount_eq_matchTotal (r gs : List Color) : nearCount r gs = matchTotal r gs := by
    induction gs generalizing r with
    | nil => simp [nearCount, matchTotal_nil]
    | cons g gs ih =>
        simp only [nearCount]
        split
        · rename_i hc
          have hmem : g ∈ r := by simpa using hc
          rw [ih]
          -- per color: min (count r) (count (g :: gs)) = indicator + min (count (r.erase g)) (count gs)
          have hpt : ∀ c, min (r.count c) ((g :: gs).count c)
                  = min ((r.erase g).count c) (gs.count c) + (if (g == c) = true then 1 else 0) := by
              intro c
              rw [List.count_erase, List.count_cons]
              by_cases hgc : g = c
              · subst hgc
                have : 0 < r.count g := List.count_pos_iff.mpr hmem
                simp; omega
              · simp [hgc]
          simp only [matchTotal]
          rw [show (fun c => min (r.count c) ((g :: gs).count c))
                  = (fun c => min ((r.erase g).count c) (gs.count c)
                        + (if (g == c) = true then 1 else 0)) from funext hpt]
          rw [sum_map_add, sum_indicator]
          omega
        · rename_i hc
          have hmem : g ∉ r := by simpa using hc
          rw [ih]
          simp only [matchTotal]
          congr 1
          apply List.map_congr_left
          intro c _
          rw [List.count_cons]
          by_cases hgc : g = c
          · subst hgc
            simp [List.count_eq_zero.mpr hmem]
          · simp [hgc]

/-- Counting a color among the pairs' first (or second) pegs splits into the
exact-match pairs plus the leftover pairs. -/
theorem count_split (f : Color × Color → Color) (ps : List (Color × Color)) (c : Color) :
        (ps.map f).count c
            = ((ps.filter (fun p => p.1 == p.2)).map f).count c
              + ((ps.filter (fun p => !(p.1 == p.2))).map f).count c := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
        by_cases hp : p.1 = p.2
        · simp [List.count_cons, hp, ih]; omega
        · simp [List.count_cons, hp, ih]; omega

/-- In an exact-match pair both pegs are the same color. -/
theorem same_snd_eq_fst (ps : List (Color × Color)) :
        (ps.filter (fun p => p.1 == p.2)).map Prod.snd
            = (ps.filter (fun p => p.1 == p.2)).map Prod.fst := by
    apply List.map_congr_left
    intro p hp
    simp at hp
    exact hp.2.symm

/-- Per color: total matches = exact matches of that color + leftover matches. -/
theorem min_split (ps : List (Color × Color)) (c : Color) :
        min ((ps.map Prod.fst).count c) ((ps.map Prod.snd).count c)
            = ((ps.filter (fun p => p.1 == p.2)).map Prod.fst).count c
              + min (((ps.filter (fun p => !(p.1 == p.2))).map Prod.fst).count c)
                    (((ps.filter (fun p => !(p.1 == p.2))).map Prod.snd).count c) := by
    rw [count_split Prod.fst ps c, count_split Prod.snd ps c, same_snd_eq_fst]
    omega

/-- Guards: full correctness of scoring, repeats included: exact + near is the
standard count-based total. Together with `eval_exact_spec` this pins down
both numbers of `eval` for every pair of codes. -/
theorem eval_total (secret guess : Code) :
        (eval secret guess).exact + (eval secret guess).near
            = (allColors.map (fun c => min (secret.toList.count c) (guess.toList.count c))).sum := by
    rw [eval_exact, eval_near]
    simp only
    rw [nearCount_eq_matchTotal]
    have hlen : secret.toList.length ≤ guess.toList.length := by simp
    have hlen' : guess.toList.length ≤ secret.toList.length := by simp
    have hfst := List.map_fst_zip hlen
    have hsnd := List.map_snd_zip hlen'
    let ps := secret.toList.zip guess.toList
    have hC : (ps.filter (fun p => p.1 == p.2)).length
            = (allColors.map (fun c => ((ps.filter (fun p => p.1 == p.2)).map Prod.fst).count c)).sum := by
        rw [sum_count, List.length_map]
    have hR : (allColors.map (fun c => min (secret.toList.count c) (guess.toList.count c))).sum
            = (allColors.map (fun c => min ((ps.map Prod.fst).count c) ((ps.map Prod.snd).count c))).sum := by
        simp only [ps]; rw [hfst, hsnd]
    rw [hR]
    simp only [matchTotal]
    rw [show (fun c => min ((ps.map Prod.fst).count c) ((ps.map Prod.snd).count c))
            = (fun c => ((ps.filter (fun p => p.1 == p.2)).map Prod.fst).count c
                + min (((ps.filter (fun p => !(p.1 == p.2))).map Prod.fst).count c)
                      (((ps.filter (fun p => !(p.1 == p.2))).map Prod.snd).count c))
            from funext (min_split ps)]
    rw [sum_map_add, ← hC]

end Mastermind
