import Mathlib

theorem algebra_20048 {x : ℝ} (hx : x ≠ 0) (h : (x * 0.6) * (x * 1.5) = (x ^ 2) * (1 - y)) :
  y = 0.1 := by 
  have eq1 : (x * 0.6) * (x * 1.5) = 0.9 * (x ^ 2) := by 
    ring
  have h1 : x^2 ≠ 0 := by
    apply pow_ne_zero 2
    exact hx
  rw [eq1] at h 
  have h2 : 0.9 = 1 - y := by
    apply (mul_left_inj' h1).mp
    linarith 
  linarith