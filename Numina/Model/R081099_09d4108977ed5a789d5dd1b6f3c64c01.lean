import Mathlib

theorem algebra_13664 (x : ℝ) :
    (Real.sin x ^ 4 + Real.cos x ^ 2 + Real.pi) / (Real.cos x ^ 4 + Real.sin x ^ 2 + Real.pi) = 1 := by
  have h1 : Real.sin x^4 + Real.cos x^2 + Real.pi = Real.cos x^4 + Real.sin x^2 + Real.pi := by
    have h2 : Real.sin x^2 = 1 - Real.cos x^2 := by
      have h3 : Real.sin x^2 + Real.cos x^2 = 1 := Real.sin_sq_add_cos_sq x
      linarith [h3]
    have h4 : Real.sin x^4 = (Real.sin x^2) ^ 2 := by ring
    rw [h4, h2]
    nlinarith [sq_nonneg (Real.cos x^2 - 1 / 2), sq_nonneg (Real.sin x^2 - 1 / 2), Real.pi_gt_three]
  have h5 : Real.cos x^4 + Real.sin x^2 + Real.pi ≠ 0 := by 
    have h6 : Real.sin x^2 ≥ 0 := by apply sq_nonneg 
    have h7 : Real.cos x^4 ≥ 0 := by positivity 
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.cos x^2 - 1 / 2), sq_nonneg (Real.sin x^2 - 1 / 2)]
  rw [show (Real.sin x ^ 4 + Real.cos x ^ 2 + Real.pi) = (Real.cos x ^ 4 + Real.sin x ^ 2 + Real.pi) by linarith [h1]]
  field_simp [h5]
  all_goals nlinarith