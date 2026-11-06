import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_597729 (f : ℝ → ℝ) (hf : f = λ x => 4 * x - 2 + 1 / (4 * x - 5)) (x : ℝ) (hx : x < 5 / 4) :
    f x ≤ 1 ∧ (∃ x : ℝ, x < 5 / 4 ∧ f x = 1) := by
  have h1 : f x = 4 * x - 2 + 1 / (4 * x - 5) := by
    rw [hf]
  constructor
  · -- First part: show f x ≤ 1
    rw [h1]
    have h2 : 4 * x - 5 < 0 := by
      linarith
    have h3 : 4 * x - 2 + 1 / (4 * x - 5) ≤ 1 := by
      have h4 : 4 * x - 2 + 1 / (4 * x - 5) - 1 ≤ 0 := by
        have h5 : 4 * x - 5 < 0 := h2
        have h6 : (4 * x - 2 + 1 / (4 * x - 5) - 1) = 
          ((4 * x - 3) * (4 * x - 5) + 1) / (4 * x - 5) := by 
          field_simp [(show 4 * x - 5 ≠ 0 by linarith)]
          ring
        rw [h6]
        have h7 : ((4 * x - 3) * (4 * x - 5) + 1) ≥ 0 := by
          have h71 : (4 * x - 3) * (4 * x - 5) + 1 = 16 * (x - 1) ^ 2 := by
            nlinarith
          rw [h71]
          nlinarith [sq_nonneg (x - 1)]
        have h8 : (4 * x - 5) < 0 := h2
        apply div_nonpos_of_nonneg_of_nonpos
        linarith
        linarith
      linarith
    linarith
  · -- Second part: existence
    use 1
    constructor
    · -- Show that 1 < 5 / 4
      norm_num
    · -- Show that f 1 = 1
      rw [hf]
      norm_num