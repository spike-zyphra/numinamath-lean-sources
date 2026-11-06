import Mathlib

theorem algebra_11281 (x : ℝ) (hx : x ≠ 0) (h : y / 100 * x = 40 / 100 * 50 / 100 * x) :
    y = 20 := by
  have h1 : y / 100 * x = (20 / 100) * x := by
    linarith
  have h2 : y / 100 = 20 / 100 := by
    apply (mul_left_inj' hx).mp
    linarith
  linarith