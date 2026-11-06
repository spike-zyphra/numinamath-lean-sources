import Mathlib

theorem algebra_252070 (x a : ℝ) (h : Real.sin x + Real.cos x = a) :
    (Real.sin x)^3 + (Real.cos x)^3 = a * (3 - a^2) / 2 := by
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  have h2 : Real.sin x * Real.cos x = (a^2 - 1) / 2 := by 
    have hsq : (Real.sin x + Real.cos x) ^ 2 = Real.sin x ^ 2 + Real.cos x ^ 2 + 2 * (Real.sin x * Real.cos x) := by 
      ring
    rw [h, h1] at hsq
    linarith
  
  have h3 : (Real.sin x) ^ 3 + (Real.cos x) ^ 3 = (Real.sin x + Real.cos x) ^ 3 - 3 * (Real.sin x * Real.cos x) * (Real.sin x + Real.cos x) := by 
    ring_nf
  
  rw [h3, h, h2]
  ring_nf