import Mathlib

theorem algebra_18746 : IsLeast {x : ℝ | (x - 3) ^ 2 - (x - 8) ^ 2 ≥ 0} (11 / 2) := by
  constructor
  · -- Show that 11/2 is in the set.
    show (11 / 2 : ℝ) ∈ {x : ℝ | (x - 3) ^ 2 - (x - 8) ^ 2 ≥ 0}
    norm_num
  · -- Show that 11/2 is the smallest element.
    intro x hx
    have h1 : (x - 3 : ℝ) ^ 2 - (x - 8 : ℝ) ^ 2 ≥ 0 := by
      simpa using hx
    nlinarith [sq_nonneg (x - (11 / 2 : ℝ) ), sq_nonneg (x - (3 : ℝ) ), sq_nonneg (x - (8 : ℝ) ) ]