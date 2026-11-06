import Mathlib

open Real Set
open scoped Real

theorem algebra_165120 {f : ℝ → ℝ} (hf : f = λ x => (cos x)^4 + (sin x)^4)
  (h : sin (2 * α) = 2 / 3) : f α = 7 / 9 := by
  have h1 : sin α * cos α = 1 / 3 := by
    have h2 : sin (2 * α) = 2 * sin α * cos α := by rw [sin_two_mul]
    rw [h2] at h
    linarith
  have h3 : (cos α)^4 + (sin α)^4 = 7 / 9 := by
    have h4 : (cos α)^2 + (sin α)^2 = 1 := by
      exact Real.cos_sq_add_sin_sq α
    have h5 : (cos α)^4 + (sin α)^4 = ((cos α)^2 + (sin α)^2)^2 - 2 * (sin α * cos α)^2 := by
      ring
    rw [h5, h4, h1]
    all_goals norm_num
  rw [hf]
  simp [h3]