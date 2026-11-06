import Mathlib

theorem algebra_96147 (x : ℝ) (h : Real.sin x = 3 * Real.cos x) :
    Real.sin x * Real.cos x = 3 / 10 := by
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : Real.sin x = 3 * Real.cos x := h
  rw [h2] at h1
  have h3 : Real.cos x ^ 2 = 1 / 10 := by
    nlinarith
  have h4 : Real.sin x * Real.cos x = 3 * Real.cos x ^ 2 := by
    have h5 : Real.sin x = 3 * Real.cos x := h2
    rw [h5]
    all_goals ring
  rw [h4]
  rw [h3]
  all_goals norm_num