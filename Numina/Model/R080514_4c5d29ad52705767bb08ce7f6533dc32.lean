import Mathlib

theorem algebra_309748 {x : ℝ} (hx : x = (Real.sqrt 5 - 3) / 2) :
    x * (x + 1) * (x + 2) * (x + 3) = -1 := by
  rw [hx]
  nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ 5 by norm_num), sq_nonneg (Real.sqrt 5 - 1), sq_nonneg (Real.sqrt 5 - 3)]