import Mathlib

theorem algebra_252097 (x : ℝ) (hx : 0 ≤ x + 16) (h : Real.sqrt (x + 16) - x + 4 = 0) :
    x = 9 := by
  have h1 : Real.sqrt (x + 16) = x - 4 := by linarith
  have h2 : 0 ≤ (x - 4) := by
    by_contra h2
    push_neg at h2
    have h3 : Real.sqrt (x + 16) ≥ 0 := by apply Real.sqrt_nonneg
    have h4 : x - 4 < 0 := by linarith
    have h5 : Real.sqrt (x + 16) < 0 := by linarith [h1, h4]
    linarith [h3, h5]
  have h3 : (Real.sqrt (x + 16)) ^ 2 = (x - 4) ^ 2 := by
    rw [h1]
  have h4 : (Real.sqrt (x + 16)) ^ 2 = x + 16 := Real.sq_sqrt (by linarith)
  rw [h4] at h3
  have h5 : x + 16 = (x - 4) ^ 2 := by 
    nlinarith
  have h6 : x ^ 2 - 9 * x = 0 := by 
    nlinarith [h5]
  have h7 : x * (x - 9) = 0 := by
    linarith [h6]
  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- x = 0, which leads to contradiction
    have h8' : x = (0 : ℝ) := by linarith
    rw [h8'] at h1
    have h9 : Real.sqrt ((0 : ℝ) + 16) ≥ 0 := by apply Real.sqrt_nonneg
    nlinarith [Real.sq_sqrt (show 0 ≤ (0 : ℝ) + 16 by linarith), 
      Real.sqrt_nonneg (0 + 16)]
  · -- x - 9 = 0, hence x = 9
    linarith