import Mathlib

theorem algebra_12311 {x : ℝ} (hx : x > 0) (h : 5 * x ^ 2 + 9 * x - 18 = 0) :
    x = 6 / 5 := by
  have h1 : 5 * x ^ 2 + 9 * x - 18 = (5 * x - 6) * (x + 3) := by 
    ring_nf
  rw [h1] at h
  cases' (mul_eq_zero.1 h) with h2 h3
  · 
    linarith
  · 
    linarith