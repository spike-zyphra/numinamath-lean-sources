import Mathlib

theorem algebra_243400 :
    IsLeast {x | ∃ t : ℝ, x = (t^2 - 4 * t + 3) * (t^2 + 4 * t + 3)} (-16) := by
  constructor
  · -- Show that -16 is in the set
    use Real.sqrt 5
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 ^ 2 - 5), sq_nonneg (Real.sqrt 5 * 4 - 4), sq_nonneg (Real.sqrt 5 * 4 + 4)]
  · -- Show that -16 is the least element in the set
    intro x hx
    rcases hx with ⟨t, ht⟩
    nlinarith [sq_nonneg (t ^ 2 - 5), sq_nonneg (t ^ 2 - 5), sq_nonneg (t * 4 - 4), sq_nonneg (t * 4 + 4)]