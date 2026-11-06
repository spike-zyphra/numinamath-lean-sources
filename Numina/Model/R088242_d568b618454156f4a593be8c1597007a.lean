import Mathlib

theorem algebra_301378 {x : ℝ} (hx : x = 1 - Real.sqrt 3) :
    x^5 - 2 * x^4 - 2 * x^3 + x^2 - 2 * x - 1 = 1 := by
  rw [hx]
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h4 : (1 - Real.sqrt 3 : ℝ) ^ 2 = 4 - 2 * Real.sqrt 3 := by
    nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3)]
  have h5 : (1 - Real.sqrt 3 : ℝ) ^ 3 = 10 - 6 * Real.sqrt 3 := by
    calc
      (1 - Real.sqrt 3 : ℝ) ^ 3 = (1 - Real.sqrt 3) * (1 - Real.sqrt 3)^2 := by ring
      _ = (1 - Real.sqrt 3) * (4 - 2 * Real.sqrt 3) := by rw [h4]
      _ = 10 - 6 * Real.sqrt 3 := by
        nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3)]
  have h6 : (1 - Real.sqrt 3 : ℝ) ^ 4 = 28 - 16 * Real.sqrt 3 := by
    calc
      (1 - Real.sqrt 3 : ℝ) ^ 4 = ((1 - Real.sqrt 3)^2) ^ 2 := by ring
      _ = (4 - 2 * Real.sqrt 3)^2 := by rw [h4]
      _ = 28 - 16 * Real.sqrt 3 := by
        nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3)]
  have h7 : (1 - Real.sqrt 3 : ℝ) ^ 5 = 76 - 44 * Real.sqrt 3 := by
    calc
      (1 - Real.sqrt 3 : ℝ) ^ 5 = (1 - Real.sqrt 3) * (1 - Real.sqrt 3)^4 := by ring
      _ = (1 - Real.sqrt 3) * (28 - 16 * Real.sqrt 3) := by rw [h6]
      _ = 76 - 44 * Real.sqrt 3 := by
        nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3)]
  nlinarith [h7, h6, h5, h4, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), h1]