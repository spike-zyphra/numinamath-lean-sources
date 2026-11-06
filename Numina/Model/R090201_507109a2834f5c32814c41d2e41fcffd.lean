import Mathlib

theorem algebra_9532 {x : ℝ} (hx : 0 ≤ x) (h : Real.sqrt x = x - 42) : x = 49 := by
  have h1 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
  have h2 : x - 42 ≥ 0 := by linarith [h, h1]
  have h3 : Real.sqrt x ^ 2 = (x - 42) ^ 2 := by 
    rw [h]
  have h4 : (Real.sqrt x) ^ 2 = x := by
    rw [Real.sq_sqrt hx]
  rw [h4] at h3
  have h5 : (x - 42) ^ 2 = x^2 - 84 * x + 1764 := by
    ring
  rw [h5] at h3
  have h6 : x^2 - 85 * x + 1764 = 0 := by
    nlinarith
  have h7 : (x - 36) * (x - 49) = 0 := by
    nlinarith [h6]
  cases' (mul_eq_zero.1 h7) with h8 h9
  · -- case $x - 36 = 0$, so $x = 36$, which contradicts $x \geq 42$
    linarith
  · -- case $x - 49 = 0$, so $x = 49$
    linarith