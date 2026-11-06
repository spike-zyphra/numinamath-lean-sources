import Mathlib

theorem algebra_13026 (θ : ℝ) (h : Real.sin (2 * θ) = 24 / 25) :
    (Real.sin θ)^4 + (Real.cos θ)^4 = 337 / 625 := by
  have h1 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := by
    rw [Real.sin_two_mul]
  rw [h1] at h
  have h2 : Real.sin θ * Real.cos θ = 12 / 25 := by
    linarith
  have h3 : (Real.sin θ) ^ 2 + (Real.cos θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h4 : (Real.sin θ) ^ 4 + (Real.cos θ) ^ 4 = (1 - 2 * (Real.sin θ * Real.cos θ) ^ 2) := by
    have h4 : (Real.sin θ) ^ 4 + (Real.cos θ) ^ 4 = ((Real.sin θ) ^ 2 + (Real.cos θ) ^ 2) ^ 2 - 2 * ((Real.sin θ) * (Real.cos θ)) ^ 2 := by
      ring
    rw [h3] at h4
    linarith
  rw [h4]
  have h5 : (Real.sin θ * Real.cos θ) ^ 2 = (12 / 25) ^ 2 := by
    rw [h2]
  rw [h5]
  norm_num