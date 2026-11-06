import Mathlib

theorem algebra_185238 (α : ℝ) : Real.sin (9 * α) + Real.sin (10 * α) + Real.sin (11 * α) + Real.sin (12 * α) =
    4 * Real.cos (α / 2) * Real.cos α * Real.sin (21 * α / 2) := by

  have h1 : Real.sin (9 * α) + Real.sin (12 * α) = 2 * Real.sin (21 * α / 2) * Real.cos (3 * α / 2) := by
    rw [show 9 * α = 21 * α / 2 - 3 * α / 2 by ring, show 12 * α = 21 * α / 2 + 3 * α / 2 by ring]
    rw [Real.sin_sub, Real.sin_add]
    ring

  have h2 : Real.sin (10 * α) + Real.sin (11 * α) = 2 * Real.sin (21 * α / 2) * Real.cos (α / 2) := by
    rw [show 10 * α = 21 * α / 2 - α / 2 by ring, show 11 * α = 21 * α / 2 + α / 2 by ring]
    rw [Real.sin_sub, Real.sin_add]
    ring

  have h3 : Real.cos (3 * α / 2) + Real.cos (α / 2) = 2 * Real.cos α * Real.cos (α / 2) := by
    have h4 : Real.cos (3 * α / 2) + Real.cos (α / 2) = 2 * Real.cos ((3 * α / 2 + α / 2) / 2) * Real.cos ((3 * α / 2 - α / 2) / 2) := by 
      rw [Real.cos_add_cos]
      <;> ring_nf
    have h5 : (3 * α / 2 + α / 2) / 2 = α := by ring
    have h6 : (3 * α / 2 - α / 2) / 2 = α / 2 := by ring
    rw [h5, h6] at h4
    rw [h4]
    all_goals ring_nf

  calc
    Real.sin (9 * α) + Real.sin (10 * α) + Real.sin (11 * α) + Real.sin (12 * α)
        = (Real.sin (9 * α) + Real.sin (12 * α)) + (Real.sin (10 * α) + Real.sin (11 * α)) := by ring
    _ = (2 * Real.sin (21 * α / 2) * Real.cos (3 * α / 2)) + (2 * Real.sin (21 * α / 2) * Real.cos (α / 2)) := by 
      rw [h1, h2]
    _ = 2 * Real.sin (21 * α / 2) * (Real.cos (3 * α / 2) + Real.cos (α / 2)) := by ring
    _ = 2 * Real.sin (21 * α / 2) * (2 * Real.cos α * Real.cos (α / 2)) := by 
      rw [show Real.cos (3 * α / 2) + Real.cos (α / 2) = 2 * Real.cos α * Real.cos (α / 2) by linarith [h3]]
    _ = 4 * Real.cos (α / 2) * Real.cos α * Real.sin (21 * α / 2) := by 
      ring