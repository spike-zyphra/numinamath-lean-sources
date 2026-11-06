import Mathlib

open Real

theorem inequalities_189400 (x : ℝ) :
    sin x ^ 6 + cos x ^ 6 ≥ 1 / 4 := by 
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq x
  
  have h2 : sin x ^ 6 + cos x ^ 6 = (sin x ^ 2 + cos x ^ 2)^3 - 3 * (sin x ^ 2 * cos x ^ 2) * (sin x ^ 2 + cos x ^ 2) := by 
    ring
  
  rw [h1] at h2
  
  have h4 : sin x ^ 6 + cos x ^ 6 = 1 - 3 * (sin x ^ 2 * cos x ^ 2) := by 
    nlinarith
  
  have h3 : sin x ^ 2 * cos x ^ 2 ≤ 1 / 4 := by 
    nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x * cos x), h1]
  
  linarith [h4, h3]