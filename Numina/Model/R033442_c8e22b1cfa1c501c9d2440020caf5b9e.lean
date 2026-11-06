import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11747 :
  {x : ℝ | 0 ≤ x ∧ 5 - sqrt x ≥ 0 ∧ 3 - sqrt (5 - sqrt x) ≥ 0} = {x | 0 ≤ x ∧ x ≤ 25} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor 
  · -- Assume x in the left side, prove right side
    rintro ⟨hx1, hx2, hx3⟩
    have h1 : sqrt x ≤ 5 := by linarith 
    have h2 : x ≤ 25 := by 
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith)]
    constructor 
    · exact hx1 
    · exact h2 
  · -- Assume x in the right side, prove left side
    rintro ⟨hx1, hx2⟩
    have h1 : sqrt x ≤ 5 := by 
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith), hx2]
    have hx2' : 5 - sqrt x ≥ 0 := by 
      linarith 
    have hx3 : sqrt (5 - sqrt x) ≤ 3 := by 
      nlinarith [Real.sqrt_nonneg (5 - sqrt x), Real.sq_sqrt (show 0 ≤ (5 - sqrt x : ℝ) by linarith), Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith)]
    have hx3' : 3 - sqrt (5 - sqrt x) ≥ 0 := by 
      linarith 
    constructor 
    · exact hx1 
    constructor 
    · exact hx2' 
    · exact hx3'