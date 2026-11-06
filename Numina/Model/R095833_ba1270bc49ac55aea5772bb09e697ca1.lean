import Mathlib

theorem algebra_12239 : Real.sqrt (3 / 8) = Real.sqrt 6 / 4 := by
  have h1 : Real.sqrt (3 / 8) ^ 2 = 3 / 8 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 6 / 4) ^ 2 = 3 / 8 := by
    calc
      (Real.sqrt 6 / 4) ^ 2 = (Real.sqrt 6) ^ 2 / 16 := by ring_nf
      _ = 6 / 16 := by rw [Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num)]
      _ = 3 / 8 := by norm_num
  have h3 : Real.sqrt (3 / 8) ≥ 0 := by positivity
  have h4 : Real.sqrt 6 / 4 ≥ 0 := by positivity
  have h5 : Real.sqrt (3 / 8) = Real.sqrt 6 / 4 := by
    have h6 : Real.sqrt (3 / 8) ^ 2 = (Real.sqrt 6 / 4) ^ 2 := by
      rw [h1, h2]
    have h7 : Real.sqrt (3 / 8) = Real.sqrt 6 / 4 := by
      nlinarith [Real.sqrt_nonneg (3 / 8), Real.sqrt_nonneg 6]
    exact h7
  exact h5