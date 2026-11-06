import Mathlib

theorem algebra_299151 (α : ℝ) : 6 * Real.sin (α / 2) ^ 2 - 8 * Real.sin (α / 2) ^ 4 =
    2 * Real.sin (3 * α / 2) * Real.sin (α / 2) := by
  have h1 : Real.sin (3 * α / 2) = 3 * Real.sin (α / 2) - 4 * Real.sin (α / 2) ^ 3 := by 
    have h2 : Real.sin (3 * α / 2) = Real.sin (3 * (α / 2)) := by ring_nf
    rw [h2]
    rw [show 3 * (α / 2) = 3 * (α / 2) by rfl]
    rw [Real.sin_three_mul]
  rw [h1]
  have h2 : 6 * Real.sin (α / 2) ^ 2 - 8 * Real.sin (α / 2) ^ 4 =
    2 * (3 * Real.sin (α / 2) - 4 * Real.sin (α / 2) ^ 3) * Real.sin (α / 2) := by
    ring
  linarith [h2]