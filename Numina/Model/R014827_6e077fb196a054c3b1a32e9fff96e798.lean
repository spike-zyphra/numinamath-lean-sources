import Mathlib

theorem algebra_186899 (α β γ φ : ℝ)
    (h₁ : Real.sin α + 7 * Real.sin β = 4 * (Real.sin γ + 2 * Real.sin φ))
    (h₂ : Real.cos α + 7 * Real.cos β = 4 * (Real.cos γ + 2 * Real.cos φ)) :
    2 * Real.cos (α - φ) = 7 * Real.cos (β - γ) := by

  have eq1 : Real.sin α = 4 * (Real.sin γ + 2 * Real.sin φ) - 7 * Real.sin β := by linarith
  have eq2 : Real.cos α = 4 * (Real.cos γ + 2 * Real.cos φ) - 7 * Real.cos β := by linarith

  have h3 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α

  rw [eq1, eq2] at h3

  have eq3 : Real.cos (α - φ) = Real.cos α * Real.cos φ + Real.sin α * Real.sin φ := by
    rw [Real.cos_sub]

  have eq4 : Real.cos (β - γ) = Real.cos β * Real.cos γ + Real.sin β * Real.sin γ := by
    rw [Real.cos_sub]

  rw [eq3, eq4]

  simp only [eq1, eq2] at *
  ring_nf at h3 ⊢
  <;> nlinarith [ Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq γ, Real.sin_sq_add_cos_sq φ ]