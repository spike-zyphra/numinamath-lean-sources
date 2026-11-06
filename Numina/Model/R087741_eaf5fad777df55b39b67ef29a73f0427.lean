import Mathlib

theorem algebra_2496 (x : ℝ) (hx : x = Real.sqrt 5 - 3) : x^3 + 5 * x^2 - 2 * x - 5 = -1 := by
  rw [hx]
  have h1 : (Real.sqrt 5 : ℝ)^2 = 5 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 5 - 3 : ℝ) ^ 2 = 14 - 6 * Real.sqrt 5 := by
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), h1]
  have h3 : (Real.sqrt 5 - 3 : ℝ) ^ 3 = 32 * Real.sqrt 5 - 72 := by
    calc
      (Real.sqrt 5 - 3 : ℝ) ^ 3 = (Real.sqrt 5 - 3) * (Real.sqrt 5 - 3)^2 := by ring
      _ = (Real.sqrt 5 - 3) * (14 - 6 * Real.sqrt 5) := by rw [h2]
      _ = 32 * Real.sqrt 5 - 72 := by
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), h1]
  nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), h1, h2, h3]