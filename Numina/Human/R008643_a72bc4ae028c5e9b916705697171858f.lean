import Mathlib

theorem algebra_232769 {x : ℝ} (hx : x > 0) (h : 56 = x * (1 + x / 100)) :
    x = 40 := by 
  have h1 : x ^ 2 + 100 * x - 5600 = 0 := by
    linarith
  have : (x - 40) * (x + 140) = 0 := by 
    rw [←h1]
    ring
  cases' (mul_eq_zero.mp this) with hx1 hx2
  · linarith
  · linarith