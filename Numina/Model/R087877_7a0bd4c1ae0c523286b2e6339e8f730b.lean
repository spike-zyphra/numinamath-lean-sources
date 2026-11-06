import Mathlib

theorem algebra_6758 {x : ℝ} (hx : x = 43 + 30 * √2) :
    √x = 5 + 3 * √2 := by
  rw [hx]
  have h1 : (5 + 3 * Real.sqrt (2 : ℝ)) ^ 2 = 43 + 30 * Real.sqrt (2 : ℝ) := by
    have h1' : (Real.sqrt (2 : ℝ) : ℝ) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ), h1']
  have h2 : (5 + 3 * Real.sqrt (2 : ℝ)) ≥ 0 := by
    have h3 : (Real.sqrt (2 : ℝ)) ≥ 0 := Real.sqrt_nonneg (2 : ℝ)
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  have h4 : Real.sqrt ((5 + 3 * Real.sqrt (2 : ℝ)) ^ 2) = (5 + 3 * Real.sqrt (2 : ℝ)) := by
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg h2]
  have h5 : Real.sqrt (43 + 30 * Real.sqrt (2 : ℝ)) = Real.sqrt ((5 + 3 * Real.sqrt (2 : ℝ)) ^ 2) := by
    rw [h1]
  rw [h5, h4]
  all_goals nlinarith