import Mathlib

theorem algebra_21909 : IsGreatest {x : ℝ | ∃ y, x^2 + y^2 = x + y} ((1 + Real.sqrt 2) / 2) := by
  constructor
  · -- Show that (1 + Real.sqrt 2)/2 is in the set
    use 1 / 2
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that (1 + Real.sqrt 2)/2 is greatest
    intro x hx
    rcases hx with ⟨y, hy⟩
    have h1 : (y - 1 / 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith [sq_nonneg (x - (1 + Real.sqrt 2) / 2), sq_nonneg (y - 1 / 2),
      Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]