import Mathlib

theorem algebra_193777 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (hxy : x = y + 40) (h : x * 2 = y * 2 + 4 * x) :
    x = 20 ∧ y = 16 := by 
  nlinarith