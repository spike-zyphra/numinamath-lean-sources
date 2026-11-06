import Mathlib

theorem algebra_259765 (x : ℝ) (hx : x^2 ≤ 0) :
    abs (1 * Real.sqrt (-x^2) - 1) - 2 * abs x = 1 := by 
  have h1 : x^2 = 0 := by
    linarith [sq_nonneg x]
  have h2 : x = 0 := by
    rw [sq_eq_zero_iff] at h1
    exact h1
  have h3 : Real.sqrt (-x^2) = 0 := by
    rw [show -x^2 = (0 : ℝ) by nlinarith]
    simp
  rw [h3, h2]
  norm_num [abs_of_nonneg]