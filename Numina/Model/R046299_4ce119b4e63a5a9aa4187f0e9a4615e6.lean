import Mathlib

theorem algebra_97214 : IsLeast {x | ∃ t : ℝ, x = (t + 1) * (t + 2) * (t + 3) * (t + 4) + 2019} 2018 := by
  constructor
  · -- Show 2018 is in the set
    use (-5 + Real.sqrt 5) / 2
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  · -- Show that 2018 is minimal
    intro x hx
    rcases hx with ⟨t, ht⟩
    nlinarith [sq_nonneg (t^2 + 5 * t + 5), sq_nonneg (t + 5 / 2), sq_nonneg ((t + 5 / 2) + (Real.sqrt 5) / 2), sq_nonneg ((t + 5 / 2) - (Real.sqrt 5) / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]