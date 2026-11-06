import Mathlib

theorem algebra_219003 (x : ℝ) (h : 3 * Real.sin x ^ 3 + Real.cos x ^ 3 = 3) :
    (Real.sin x) ^ 2018 + (Real.cos x) ^ 2018 = 1 := by
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : Real.sin x ≥ 0 := by
    nlinarith [sq_nonneg (Real.sin x ^ 2 - 1), sq_nonneg (Real.cos x ^ 2 - 1), sq_nonneg (Real.sin x - Real.cos x), sq_nonneg (Real.sin x), sq_nonneg (Real.sin x - 1), sq_nonneg (Real.cos x ^ 2 - 0), sq_nonneg (Real.sin x * Real.sin x * Real.sin x), sq_nonneg ((Real.sin x * Real.sin x) - (Real.sin x * 1)), sq_nonneg (Real.sin x -1), sq_nonneg (Real.sin x +1), sq_nonneg (Real.cos x ^ 2 - Real.sin x ^ 2), sq_nonneg (Real.sin x * Real.sin x - Real.sin x * Real.cos x), Real.sin_sq_add_cos_sq x]
  have h3 : Real.cos x ≥ 0 := by
    nlinarith [sq_nonneg (Real.sin x ^ 2 - 1), sq_nonneg (Real.cos x ^ 2 - 1), sq_nonneg (Real.sin x - Real.cos x), sq_nonneg (Real.sin x), sq_nonneg (Real.sin x - 1), sq_nonneg (Real.cos x ^ 2 - 0), sq_nonneg (Real.sin x * Real.sin x * Real.sin x), sq_nonneg ((Real.sin x * Real.sin x) - (Real.sin x * 1)), sq_nonneg (Real.sin x -1), sq_nonneg (Real.sin x +1), sq_nonneg (Real.cos x ^ 2 - Real.sin x ^ 2), sq_nonneg (Real.sin x * Real.sin x - Real.sin x * Real.cos x), Real.sin_sq_add_cos_sq x]

  have h4 : Real.sin x = 1 := by
    nlinarith [sq_nonneg (Real.sin x - 1), sq_nonneg (Real.cos x - 0), sq_nonneg (Real.sin x ^ 2 - 1), sq_nonneg (Real.sin x * Real.sin x - 1), sq_nonneg (Real.sin x * Real.sin x - Real.sin x), sq_nonneg (Real.cos x ^ 2 - Real.sin x), Real.sin_sq_add_cos_sq x, sq_nonneg ((Real.sin x - 1) * (Real.sin x - 1)), sq_nonneg ((Real.sin x * 0 - Real.sin x * Real.sin x)), sq_nonneg (Real.sin x ^ 2 + Real.cos x ^ 2 - 1)]

  have h5 : Real.cos x = 0 := by
    have h6 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    rw [show Real.sin x = 1 by linarith [h4]] at h6
    nlinarith [ Real.sin_sq_add_cos_sq x, sq_nonneg (Real.cos x) ]
  rw [h4, h5]
  norm_num