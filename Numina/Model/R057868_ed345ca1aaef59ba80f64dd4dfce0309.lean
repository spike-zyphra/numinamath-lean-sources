import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_13464 (x : ℝ) :
  (x + 6) / (x ^ 2 + 2 * x + 7) ≥ 0 ↔ x ≥ -6 := by 
  have h1 : x ^ 2 + 2 * x + 7 > 0 := by 
    nlinarith [sq_nonneg (x + 1)]
  have h2 : (x + 6) / (x ^ 2 + 2 * x + 7) ≥ 0 ↔ x + 6 ≥ 0 := by 
    constructor
    · -- Assume (x + 6) / (x ^ 2 + 2 * x + 7) ≥ 0, prove x + 6 ≥ 0
      intro h
      apply div_nonneg_iff.mp at h
      cases h with
      | inl h1 =>
        linarith
      | inr h2 =>
        linarith
    · -- Assume x + 6 ≥ 0, prove (x + 6) / (x ^ 2 + 2 * x + 7) ≥ 0
      intro h
      apply div_nonneg 
      linarith
      all_goals nlinarith
  rw [h2]
  constructor
  · -- Assume x + 6 ≥ 0, prove x ≥ -6 
    intro h
    linarith 
  · -- Assume x ≥ -6, prove x + 6 ≥ 0 
    intro h
    linarith