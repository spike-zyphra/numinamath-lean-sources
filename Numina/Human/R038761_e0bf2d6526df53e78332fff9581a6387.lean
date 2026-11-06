import Mathlib

/- Simplify
\[\cos ^2 x + \cos^2 (x + y) - 2 \cos x \cos y \cos (x + y).\] -/
theorem calculus_16912 (x y : ℝ) :
    Real.cos x ^ 2 + Real.cos (x + y) ^ 2 - 2 * Real.cos x * Real.cos y * Real.cos (x + y) =
    Real.sin y ^ 2 := by
  rw [Real.cos_add]
  ring_nf
  simp only [Real.cos_sq, Real.sin_sq]
  ring