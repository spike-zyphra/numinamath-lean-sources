import Mathlib

theorem algebra_322526 {x y : ℝ} (h1 : x^2 + x * y + y = 14) (h2 : y^2 + x * y + x = 28) :
    x + y = 6 ∨ x + y = -7 := by 
  have h3 : (x + y) ^ 2 + (x + y) = 42 := by 
    nlinarith [h1, h2]
  have h4 : (x + y - 6) * (x + y + 7) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case where $x + y - 6 = 0$, so $x + y = 6$
    left
    linarith
  · -- Case where $x + y + 7 = 0$, so $x + y = -7$
    right
    linarith