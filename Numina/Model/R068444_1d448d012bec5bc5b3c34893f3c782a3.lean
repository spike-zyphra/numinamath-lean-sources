import Mathlib

theorem algebra_13527 {x : ℝ} (hx : x ≥ 0) (h : Real.sqrt x = x - 90) :
    x = 100 := by
  have h1 : x - 90 ≥ 0 := by 
    have h9 : Real.sqrt x ≥ 0 := by positivity
    linarith
  have h2 : Real.sqrt x ≥ 0 := by positivity
  have h3 : (Real.sqrt x) ^ 2 = (x - 90) ^ 2 := by 
    rw [h]
  have h4 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith [hx])
  rw [h4] at h3
  have h5 : x = (x - 90) ^ 2 := by 
    nlinarith [h3]
  have h6 : x ^ 2 - 181 * x + 8100 = 0 := by
    nlinarith [h5]
  have h7 : (x - 100) * (x - 81) = 0 := by
    nlinarith [h6]
  cases' (mul_eq_zero.mp h7) with h8 h9
  · 
    linarith
  · 
    have h10 : x = 81 := by linarith
    nlinarith [Real.sqrt_nonneg x, h10, show x - 90 ≥ 0 by linarith [h1]]