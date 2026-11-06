import Mathlib

theorem algebra_248599 {x : ℝ} (hx : x > 0) (h : (x - 2) * (x * 1.2) = x * x) :
    x = 12 := by 
  ring_nf at h
  have h2 : x * (x - 12) = 0 := by 
    linarith
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case x = 0, contradicts x > 0
    linarith
  · -- Case x - 12 = 0, thus x = 12
    linarith