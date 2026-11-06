import Mathlib

theorem algebra_241178 {x y : ℝ} (hx : 0 < x) (hy : x < y) (h : x^2 + 4 * y^2 = 5 * x * y) :
    (x + 2 * y) / (x - 2 * y) = -3 := by
  have h1 : (x - y) * (x - 4 * y) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp h1) with h1a h1b
  · -- Case $x - y = 0$
    have h_eq : x = y := by linarith
    linarith [show x < y from hy, show x = y from h_eq]
  · -- Case $x - 4y = 0$
    have h_eq : x = 4 * y := by linarith
    nlinarith [show 0 < x from hx, show x < y from hy, show x = 4 * y from h_eq]