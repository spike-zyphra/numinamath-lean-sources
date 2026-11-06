import Mathlib

open Real

theorem inequalities_12341 (a : ℝ) (ha : ∀ x y : ℝ, x > 0 → y > 0 → sqrt x + sqrt y ≤ a * sqrt (x + y)) :
    a ≥ sqrt 2 := by
  have h1 := ha 1 1 (by norm_num) (by norm_num)
  have h2 : sqrt 1 + sqrt 1 = 2 := by
    simp [sqrt_one]
    all_goals norm_num
  have h3 : sqrt (1 + 1 : ℝ) = Real.sqrt 2 := by norm_num
  rw [h2, h3] at h1
  have h5 : Real.sqrt 2 > 0 := by positivity
  have h6 : a ≥ Real.sqrt 2 := by
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  exact h6