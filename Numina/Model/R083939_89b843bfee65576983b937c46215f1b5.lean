import Mathlib

theorem algebra_139685 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (1 - 50 / 100) * (1 - 50 / 100) * x = (1 - y / 100) * x) :
    y = 75 := by
  have h1 : (1 - 50 / 100 : ℝ) * (1 - 50 / 100) * x = (1 - y / 100) * x := by
    linarith
  have eq1 : (1 - 50 / 100 : ℝ) * (1 - 50 / 100) = (1 - y / 100) := by
    apply (mul_left_inj' hx).mp
    linarith
  norm_num at eq1 
  linarith