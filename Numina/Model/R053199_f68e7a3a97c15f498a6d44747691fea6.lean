import Mathlib

theorem algebra_177511 (x : ℝ) (h : Real.sin x ^ 3 - Real.cos x ^ 3 = -1) :
    Real.sin x - Real.cos x = -1 := by
  have h1 : Real.sin x ^ 3 - Real.cos x ^ 3 = (Real.sin x - Real.cos x) ^ 3 + 3 * (Real.sin x * Real.cos x) * (Real.sin x - Real.cos x) := by 
    ring
  rw [h1] at h
  have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h3 : Real.sin x * Real.cos x = (1 - (Real.sin x - Real.cos x) ^ 2) / 2 := by
    have h4 : (Real.sin x - Real.cos x) ^ 2 = Real.sin x^2 + Real.cos x^2 - 2 * (Real.sin x * Real.cos x) := by 
      ring
    rw [show Real.sin x^2 + Real.cos x^2 = 1 by linarith [h2]] at h4
    nlinarith
    all_goals nlinarith [Real.sin_sq_add_cos_sq x]
  rw [h3] at h
  have h4 : (Real.sin x - Real.cos x) ^ 3 - 3 * (Real.sin x - Real.cos x) - 2 = 0 := by 
    nlinarith [h]
  have h5 : (Real.sin x - Real.cos x + 1) ^ 2 * (Real.sin x - Real.cos x - 2) = 0 := by
    nlinarith [sq_nonneg (Real.sin x - Real.cos x + 1), sq_nonneg (Real.sin x - Real.cos x - 2), h4]
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case where (Real.sin x - Real.cos x + 1) ^ 2 = 0
    have h8 : Real.sin x - Real.cos x + 1 = 0 := by
      apply pow_eq_zero 
      exact h6
    linarith
  · -- Case where Real.sin x - Real.cos x - 2 = 0
    have h8 : Real.sin x - Real.cos x = 2 := by linarith
    have h9 : Real.sin x ≤ 1 := Real.sin_le_one x
    have h10 : Real.cos x ≤ 1 := Real.cos_le_one x
    have h11 : Real.sin x ≥ -1 := Real.neg_one_le_sin x
    have h12 : Real.cos x ≥ -1 := Real.neg_one_le_cos x
    nlinarith [Real.sin_sq_add_cos_sq x, h8, h9, h10, h11, h12]