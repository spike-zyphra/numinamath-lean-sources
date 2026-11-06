import Mathlib

theorem algebra_72 : -Real.sqrt 2 / 2 + 2 * (-Real.sqrt 2 / 2)^2 - 4 * (-Real.sqrt 2 / 2)^4 = -Real.sqrt 2 / 2 := by
  have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
  have h2 : (-Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    nlinarith [h1]
  have h3 : (-Real.sqrt 2 / 2) ^ 4 = 1 / 4 := by
    calc
      (-Real.sqrt 2 / 2) ^ 4 = ((-Real.sqrt 2 / 2) ^ 2) ^ 2 := by ring
      _ = (1 / 2) ^ 2 := by rw [h2]
      _ = 1 / 4 := by norm_num
  nlinarith [h2, h3, Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]