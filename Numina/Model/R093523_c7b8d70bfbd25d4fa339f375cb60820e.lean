import Mathlib

open Real

theorem algebra_1642 {x : ℝ} (hx : x = (sqrt 33 - 5) / 2) : (x + 1) * (x + 2) * (x + 3) * (x + 4) = 48 := by
  rw [hx]
  nlinarith [Real.sqrt_nonneg 33, Real.sq_sqrt (show (0 : ℝ) ≤ 33 by norm_num)]