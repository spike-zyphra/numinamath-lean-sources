import Mathlib

theorem calculus_16882 : Real.sin (4 * x) + Real.sin (6 * x) = 2 * Real.sin (5 * x) * Real.cos x := by 
  have h1 : Real.sin (4 * x) + Real.sin (6 * x) = 2 * Real.sin (5 * x) * Real.cos x := by 
    rw [show 4 * x = 5 * x - x by ring, show 6 * x = 5 * x + x by ring]
    rw [Real.sin_sub, Real.sin_add]
    ring
  exact h1