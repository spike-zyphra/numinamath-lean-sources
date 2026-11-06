import Mathlib

theorem algebra_9536 {x : ℝ} (hx : x = Real.sqrt (20 - Real.sqrt 396)) :
    x = Real.sqrt 11 - 3 := by
  have h1 : Real.sqrt 396 = 6 * Real.sqrt 11 := by
    calc
      Real.sqrt 396 = Real.sqrt (6^2 * 11) := by norm_num
      _ = Real.sqrt (6^2) * Real.sqrt 11 := by rw [Real.sqrt_mul (by norm_num)]
      _ = 6 * Real.sqrt 11 := by rw [Real.sqrt_sq (by norm_num)]
  rw [hx, h1]

  have h2 : Real.sqrt 11 - 3 ≥ 0 := by
    have h3 : Real.sqrt 11 ≥ Real.sqrt 9 := Real.sqrt_le_sqrt (by norm_num)
    have h4 : Real.sqrt 9 = 3 := Real.sqrt_eq_cases.2 (by norm_num)
    have h5 : Real.sqrt 11 ≥ 0 := Real.sqrt_nonneg 11
    linarith [h3, h4, Real.sqrt_pos.mpr (show (0:ℝ) < 11 by norm_num : (0:ℝ) < 11)]

  have h5 : (Real.sqrt 11 - 3) ^ 2 = 20 - 6 * Real.sqrt 11 := by
    calc 
      (Real.sqrt 11 - 3) ^ 2 = (Real.sqrt 11) ^ 2 - 2 * (Real.sqrt 11 * 3) + 3 ^ 2 := by ring
      _ = 11 - 6 * Real.sqrt 11 + 9 := by simp [Real.sq_sqrt]; all_goals linarith
      _ = 20 - 6 * Real.sqrt 11 := by ring

  rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [h5, h2, Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num : (0 : ℝ) ≤ 11)]