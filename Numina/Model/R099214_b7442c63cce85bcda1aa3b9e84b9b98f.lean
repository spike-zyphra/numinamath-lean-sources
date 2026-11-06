import Mathlib

theorem calculus_13989 (θ : ℝ) (h : Real.sin (2 * θ) = 1 / 3) :
    (Real.sin θ)^6 + (Real.cos θ)^6 = 11 / 12 := by
  have h1 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  rw [h1] at h
  have h2 : Real.sin θ * Real.cos θ = 1 / 6 := by
    linarith
  have h3 : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := Real.sin_sq_add_cos_sq θ
  have h4 : (Real.sin θ)^6 + (Real.cos θ)^6 = 1 - 3 * ((Real.sin θ * Real.cos θ)^2) := by
    have h5 : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := h3
    have h6 : (Real.sin θ)^6 + (Real.cos θ)^6 = ((Real.sin θ)^2 + (Real.cos θ)^2)^3 - 3 * ((Real.sin θ)^2 + (Real.cos θ)^2) * ((Real.sin θ * Real.cos θ)^2) := by
      ring_nf
    rw [h5] at h6
    linarith
  rw [h4, h2]
  all_goals norm_num