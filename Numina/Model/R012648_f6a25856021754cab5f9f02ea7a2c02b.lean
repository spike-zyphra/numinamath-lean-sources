import Mathlib

theorem algebra_186082 (α : Real) :
    Real.sin (2 * α) + Real.sin (4 * α) + Real.sin (6 * α) =
    4 * Real.sin (3 * α) * Real.cos (2 * α) * Real.cos α := by

  have h1 : Real.sin (2 * α) + Real.sin (4 * α) = 2 * Real.sin (3 * α) * Real.cos α := by
    have h4 : Real.sin (4 * α) = Real.sin (3 * α + α) := by ring_nf
    have h5 : Real.sin (2 * α) = Real.sin (3 * α - α) := by ring_nf
    rw [h4, h5]
    have h6 : Real.sin (3 * α + α) = Real.sin (3 * α) * Real.cos α + Real.cos (3 * α) * Real.sin α := by
      rw [Real.sin_add]
    have h7 : Real.sin (3 * α - α) = Real.sin (3 * α) * Real.cos α - Real.cos (3 * α) * Real.sin α := by
      rw [Real.sin_sub]
    rw [h6, h7]
    ring_nf

  have h2 : Real.sin (6 * α) = 2 * Real.sin (3 * α) * Real.cos (3 * α) := by
    have h3 : Real.sin (6 * α) = Real.sin (2 * (3 * α)) := by ring_nf
    rw [h3]
    rw [Real.sin_two_mul]
    all_goals ring_nf

  have h3 : Real.cos (3 * α) = 4 * Real.cos α ^ 3 - 3 * Real.cos α := by
    rw [Real.cos_three_mul]

  have h4 : Real.cos α + Real.cos (3 * α) = 2 * Real.cos (2 * α) * Real.cos α := by
    have h5 : Real.cos α + Real.cos (3 * α) = 4 * Real.cos α ^ 3 - 2 * Real.cos α := by
      rw [h3]
      ring_nf
    have hcos2 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by
      rw [Real.cos_two_mul]
    have h6 : 2 * Real.cos (2 * α) * Real.cos α = 4 * Real.cos α ^ 3 - 2 * Real.cos α := by
      rw [hcos2]
      ring_nf
    rw [h5, h6]

  calc
    Real.sin (2 * α) + Real.sin (4 * α) + Real.sin (6 * α)
        = (Real.sin (2 * α) + Real.sin (4 * α)) + Real.sin (6 * α) := by ring_nf
    _ = 2 * Real.sin (3 * α) * Real.cos α + Real.sin (6 * α) := by
      rw [h1]
    _ = 2 * Real.sin (3 * α) * Real.cos α + 2 * Real.sin (3 * α) * Real.cos (3 * α) := by
      rw [h2]
    _ = 2 * Real.sin (3 * α) * (Real.cos α + Real.cos (3 * α)) := by ring_nf
    _ = 2 * Real.sin (3 * α) * (2 * Real.cos (2 * α) * Real.cos α) := by
      rw [h4]
    _ = 4 * Real.sin (3 * α) * Real.cos (2 * α) * Real.cos α := by
      ring_nf