import Mathlib

theorem algebra_322625 {x y : ℝ} (hx : x = Real.sqrt 3 + 1) (hy : y = 2 * x^5 - 4 * x^4 - x^3 - 6 * x^2 - 6) :
    y = 6 * Real.sqrt 3 := by
  rw [hy, hx]
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 3 ^ 4 = 9 := by
    calc
      Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = (3) ^ 2 := by rw [h1]
      _ = 9 := by norm_num
  ring_nf
  <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show 3 > 0 by norm_num), h1, h2, sq_nonneg (Real.sqrt 3 - 1), sq_nonneg (Real.sqrt 3)]