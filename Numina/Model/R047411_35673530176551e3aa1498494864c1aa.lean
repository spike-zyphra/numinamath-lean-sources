import Mathlib

theorem algebra_13403 {x : ℝ} (hx : x ≥ 0) (h : Real.sqrt x = x - 30) :
    x = 36 := by
  have h1 : Real.sqrt x ≥ 0 := by
    apply Real.sqrt_nonneg
  have h2 : x ≥ 30 := by
    nlinarith [h, Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith)]
  have h3 : Real.sqrt x ^ 2 = (x - 30) ^ 2 := by
    rw [h]
  have h4 : Real.sqrt x ^ 2 = x := by 
    rw [Real.sq_sqrt]
    linarith
  rw [h4] at h3
  have h5 : x^2 - 61 * x + 900 = 0 := by
    nlinarith
  have h6 : (x - 36) * (x - 25) = 0 := by 
    nlinarith [h5]
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- x - 36 = 0, so x = 36
    linarith 
  · -- x - 25 = 0, so x = 25, which contradicts since x ≥ 30
    have h9 : x = 25 := by linarith
    rw [h9] at h 
    nlinarith [Real.sqrt_nonneg 25, Real.sq_sqrt (show (0 : ℝ) ≤ 25 by norm_num)]