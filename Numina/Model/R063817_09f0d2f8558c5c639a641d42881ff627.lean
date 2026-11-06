import Mathlib

open Real

theorem algebra_287228 (α β γ : ℝ) :
    sin α ^ 3 * sin (β - γ) ^ 3 +
    sin β ^ 3 * sin (γ - α) ^ 3 +
    sin γ ^ 3 * sin (α - β) ^ 3 =
    3 * sin α * sin β * sin γ * sin (α - β) * sin (β - γ) * sin (γ - α) := by
  simp [sin_sub, cos_sub]
  ring_nf
  <;> simp [sin_sq, cos_sq]
  <;> ring_nf
  <;> simp [sin_sq, cos_sq]
  <;> ring