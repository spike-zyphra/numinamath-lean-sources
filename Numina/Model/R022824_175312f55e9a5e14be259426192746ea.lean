import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_187076 (x : ℝ) (hx : x ≠ 1) :
  5 * x ^ 2 / (x - 1) > 5 * x + 1 ↔ x < -1 / 4 ∨ x > 1 := by
  constructor
  · -- Assume 5 * x ^ 2 / (x - 1) > 5 * x + 1, prove x < -1 / 4 ∨ x > 1
    intro h
    by_cases h1 : (x - 1) > 0
    · -- When x - 1 > 0, i.e., x > 1:
      -- Multiply both sides by (x - 1) to get 5 * x ^ 2 > (5 * x + 1) * (x - 1)
      have h3 : 5 * x ^ 2 > (5 * x + 1) * (x - 1) := by
        have h2 : 5 * x ^ 2 / (x - 1) > 5 * x + 1 := h
        apply (lt_div_iff₀ h1).mp at h2
        linarith
      have h2x : x > 1 := by nlinarith
      right
      tauto
    · -- Case where (x - 1) ≤ 0
      push_neg at h1
      have h4 : x - 1 < 0 := by
        by_contra h5
        push_neg at h5
        have h6 : x - 1 = 0 := by
          linarith
        have h7 : x = 1 := by linarith
        contradiction
      -- Multiply both sides by (x - 1), reversing the inequality
      -- to get 5 * x ^ 2 < (5 * x + 1) * (x - 1)
      have h5 : 5 * x ^ 2 < (5 * x + 1) * (x - 1) := by
        have h2 : 5 * x ^ 2 / (x - 1) > 5 * x + 1 := h
        apply (lt_div_iff_of_neg' (by linarith)).mp at h2
        linarith
      -- The inequality simplifies to x < -1/4
      have h6 : x < -1 / 4 := by nlinarith
      left
      tauto
  · -- Assume x < -1 / 4 ∨ x > 1, prove 5 * x ^ 2 / (x - 1) > 5 * x + 1
    rintro (h | h)
    · -- Case x < -1 / 4
      have h1 : x < -1 / 4 := h
      have h4 : x - 1 < 0 := by linarith
      -- Convert the inequality to the form with divisor
      -- Multiply by (x - 1) (negative), reversing inequality
      -- 5 * x ^ 2 < (5 * x + 1) * (x - 1)
      have h5 : 5 * x ^ 2 < (5 * x + 1) * (x - 1) := by nlinarith
      have h6 : 5 * x ^ 2 / (x - 1) > 5 * x + 1 := by 
        apply (lt_div_iff_of_neg' (by linarith)).mpr
        linarith
      exact h6
    · -- Case x > 1
      have h2 : x > 1 := h
      have h4 : x - 1 > 0 := by linarith
      -- Convert to form with divisor. Multiply by (x-1) preserves inequality.
      -- 5 * x^2 > (5 * x +1) * (x -1)
      have h5 : 5 * x ^ 2 > (5 * x + 1) * (x - 1) := by nlinarith
      have h6 : 5 * x ^ 2 / (x - 1) > 5 * x + 1 := by 
        apply (lt_div_iff₀ (by linarith)).mpr
        linarith
      exact h6