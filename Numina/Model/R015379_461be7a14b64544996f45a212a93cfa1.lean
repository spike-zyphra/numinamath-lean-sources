import Mathlib

open Real Set
open scoped Real

theorem algebra_299214 (α β γ : ℝ)
  (h₁ : sin α + sin β + sin γ = 0) (h₂ : cos α + cos β + cos γ = 0) :
  (cos α)^2 + (cos β)^2 + (cos γ)^2 = 3 / 2 := by
  have h3 : sin α = - (sin β + sin γ) := by
    linarith
  have h4 : cos α = - (cos β + cos γ) := by
    linarith
  have h5 : sin α ^ 2 + cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α
  have h6 : sin β ^ 2 + cos β ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq β
  have h7 : sin γ ^ 2 + cos γ ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq γ
  rw [h3, h4] at h5
  have eq1 : (sin β + sin γ) ^ 2 + (cos β + cos γ) ^ 2 = 1 := by
    nlinarith [h5]
  have eq2 : (cos α) ^ 2 + (cos β) ^ 2 + (cos γ) ^ 2 = 3 / 2 := by
    have eq3 : (cos α) ^ 2 = (cos β + cos γ) ^ 2 := by
      rw [h4]
      ring
    rw [eq3]
    nlinarith [h6, h7, eq1]
  linarith [eq2]