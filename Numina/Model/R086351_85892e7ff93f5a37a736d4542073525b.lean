import Mathlib

theorem algebra_260505 (x : ℝ) (h : Real.sin x + Real.cos x = 1 / 2) :
    (Real.sin x)^3 + (Real.cos x)^3 = 11 / 16 := by 
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : Real.sin x * Real.cos x = -3 / 8 := by
    have hsq : (Real.sin x + Real.cos x) ^ 2 = (1 / 2) ^ 2 := by
      rw [h]
    have hexp : (Real.sin x + Real.cos x) ^ 2 = Real.sin x ^ 2 + Real.cos x ^ 2 + 2 * (Real.sin x * Real.cos x) := by 
      ring
    rw [hexp] at hsq
    rw [h1] at hsq
    linarith
  have h3 : (Real.sin x + Real.cos x) ^ 3 = (1 / 2) ^ 3 := by
    rw [h]
  have hexp2 : (Real.sin x + Real.cos x) ^ 3 = (Real.sin x)^3 + (Real.cos x)^3 + 3 * (Real.sin x * Real.cos x) * (Real.sin x + Real.cos x) := by
    ring
  rw [hexp2] at h3
  rw [h, h2] at h3
  linarith