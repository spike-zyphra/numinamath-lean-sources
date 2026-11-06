import Mathlib

open Real Set
open scoped Real

theorem algebra_196617 (α : ℝ) :
  ∃ c, ∀ φ : ℝ, 4 * cos α * cos φ * cos (α - φ) +
    2 * (sin (α - φ))^2 - cos (2 * φ) = c := by 
  use 2 * (cos α) ^ 2 + 1
  intro φ
  have h1 : cos (α - φ) = cos α * cos φ + sin α * sin φ := by 
    rw [cos_sub]
  have h2 : sin (α - φ) = sin α * cos φ - cos α * sin φ := by 
    rw [sin_sub]
  have h3 : cos (2 * φ) = 2 * (cos φ) ^ 2 - 1 := by 
    rw [cos_two_mul]
  rw [h1, h2, h3]
  have eq1 : sin α ^ 2 = 1 - cos α ^ 2 := by 
    rw [← Real.sin_sq_add_cos_sq α]
    linarith
  have eq2 : sin φ ^ 2 = 1 - cos φ ^ 2 := by 
    rw [← Real.sin_sq_add_cos_sq φ]
    linarith
  ring_nf
  <;> simp [sin_sq, cos_sq, eq1, eq2]
  <;> ring