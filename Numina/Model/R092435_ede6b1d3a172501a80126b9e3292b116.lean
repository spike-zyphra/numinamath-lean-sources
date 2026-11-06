import Mathlib

theorem algebra_162222 (α φ : ℝ) :
    4 * Real.cos α * Real.cos φ * Real.cos (α - φ) - 2 * (Real.cos (α - φ))^2 - Real.cos (2 * φ) =
    Real.cos (2 * α) := by 
  rw [Real.cos_sub, Real.cos_two_mul, Real.cos_two_mul]
  ring_nf
  <;> simp [Real.cos_sq, Real.sin_sq]
  <;> ring