import Mathlib

open Real Set
open scoped Real

theorem algebra_162235 (α φ : ℝ) :
  sin φ ^ 2 - cos (α - φ) ^ 2 + 2 * cos α * cos φ * cos (α - φ) = cos α ^ 2 := by
  have h1 : cos (α - φ) = cos α * cos φ + sin α * sin φ := by
    rw [cos_sub]
  rw [h1]
  ring_nf
  <;> simp [sin_sq, cos_sq]
  <;> ring_nf
  <;> simp [sin_sq, cos_sq]
  <;> ring_nf