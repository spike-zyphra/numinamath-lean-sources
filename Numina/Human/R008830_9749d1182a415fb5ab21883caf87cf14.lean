import Mathlib

/- Express $\sin 4x + \sin 6x$ as a product of trigonometric functions. -/
theorem calculus_16882 : Real.sin (4 * x) + Real.sin (6 * x) = 2 * Real.sin (5 * x) * Real.cos x := by
  have h1 : Real.sin (4 * x) + Real.sin (6 * x) = Real.sin (5 * x + x) + Real.sin (5 * x - x) := by ring
  rw [h1]
  simp only [Real.sin_add, Real.sin_sub]
  ring_nf