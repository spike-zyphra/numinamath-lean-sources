import Mathlib

theorem algebra_200573 (x y : ℝ) (h₀ : Real.sin x + Real.sin y = 0.6) (h₁ : Real.cos x + Real.cos y = 0.8) :
    Real.cos x * Real.cos y = -11/100 := by
  have h2 : (Real.sin x + Real.sin y) ^ 2 + (Real.cos x + Real.cos y) ^ 2 = (0.6 : ℝ) ^ 2 + (0.8 : ℝ) ^ 2 := by
    rw [h₀, h₁]
  have h3 : (Real.sin x + Real.sin y) ^ 2 + (Real.cos x + Real.cos y) ^ 2 = 
          (Real.sin x)^2 + (Real.sin y)^2 + 2 * (Real.sin x * Real.sin y) + (Real.cos x)^2 + (Real.cos y)^2 + 2 * (Real.cos x * Real.cos y) := by
    ring
  rw [h3] at h2
  have h4 : (Real.sin x) ^ 2 + (Real.cos x) ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h5 : (Real.sin y) ^ 2 + (Real.cos y) ^ 2 = 1 := Real.sin_sq_add_cos_sq y
  have h7 : Real.sin y = 0.6 - Real.sin x := by linarith
  have h8 : Real.cos y = 0.8 - Real.cos x := by linarith
  have h9 : (Real.sin y) ^ 2 + (Real.cos y) ^ 2 = 1 := Real.sin_sq_add_cos_sq y
  rw [h7, h8] at h9
  ring_nf at h2 h9 h4
  nlinarith [Real.sin_sq_add_cos_sq x]