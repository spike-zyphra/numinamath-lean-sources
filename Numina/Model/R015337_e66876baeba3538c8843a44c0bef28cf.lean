import Mathlib

theorem algebra_280658 {x y z : ℝ} (h : x + y + z - 2*(x*y + y*z + x*z) + 4*x*y*z = 1/2) :
    x = 1/2 ∨ y = 1/2 ∨ z = 1/2 := by

  have eq : (2 * x - 1) * (2 * y - 1) * (2 * z - 1) = 0 := by 
    linarith [h]

  cases' (mul_eq_zero.mp eq) with h1 h2
  cases' (mul_eq_zero.mp h1) with h3 h4
  · -- Case $2x - 1 = 0$, so $x = 1/2$
    left
    linarith
  · -- Case $2y - 1 = 0$, so $y = 1/2$
    right
    left
    linarith
  · -- Case $2z - 1 = 0$, so $z = 1/2$
    right
    right
    linarith