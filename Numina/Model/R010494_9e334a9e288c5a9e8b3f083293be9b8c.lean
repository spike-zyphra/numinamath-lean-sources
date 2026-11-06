import Mathlib

theorem algebra_13359 {x y : ℝ} (hx : x + y = 1000) (hy : (1 + 3 / 100) ^ 2 * x + (1 + 5 / 100) ^ 2 * y = 1090.02) :
    x = 300 := by
  have h1 : y = 1000 - x := by linarith
  rw [h1] at hy
  norm_num at hy
  linarith