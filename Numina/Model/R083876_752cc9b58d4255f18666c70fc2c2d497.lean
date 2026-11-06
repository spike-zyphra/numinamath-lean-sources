import Mathlib

open Real Set

theorem inequalities_11928 (x y : ℝ) (h : x^2 + y^2 ≤ 1) :
    x + y - x * y ≤ 1 ∧ ∃ x y, x^2 + y^2 = 1 ∧ x + y - x * y = 1 := by
  constructor
  · -- Show the first part
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y), sq_nonneg (x + y - 1)]
  · -- Show the existence in the second part.
    refine' ⟨1, 0, ?_, ?_⟩
    · -- Verify the constraint
      norm_num
    · -- Verify the value
      norm_num