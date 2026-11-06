import Mathlib

open Real

theorem algebra_185227 (α : ℝ) :
    cos α + cos (2 * α) + cos (6 * α) + cos (7 * α) =
    4 * cos (α / 2) * cos (5 * α / 2) * cos (4 * α) := by

  have h1 : cos α + cos (7 * α) = 2 * cos (4 * α) * cos (3 * α) := by
    have h2 : cos α + cos (7 * α) = 2 * cos (4 * α) * cos (3 * α) := by
      have h5 : cos α = cos (4 * α - 3 * α) := by ring_nf
      have h6 : cos (7 * α) = cos (4 * α + 3 * α) := by ring_nf
      rw [h5, h6]
      rw [cos_sub, cos_add]
      ring
    linarith

  have h2 : cos (2 * α) + cos (6 * α) = 2 * cos (4 * α) * cos (2 * α) := by
    have h3 : cos (2 * α) + cos (6 * α) = 2 * cos (4 * α) * cos (2 * α) := by
      have h7 : cos (2 * α) + cos (6 * α) = 2 * cos (4 * α) * cos (2 * α) := by
        have h8 : cos (2 * α) + cos (6 * α) = cos (4 * α - 2 * α) + cos (4 * α + 2 * α) := by
          ring_nf
        rw [h8]
        have h9 : cos (4 * α - 2 * α) = cos (4 * α) * cos (2 * α) + sin (4 * α) * sin (2 * α) := by
          rw [cos_sub]
        have h10 : cos (4 * α + 2 * α) = cos (4 * α) * cos (2 * α) - sin (4 * α) * sin (2 * α) := by
          rw [cos_add]
        rw [h9, h10]
        ring
      linarith
    linarith

  have h3 : cos (3 * α) + cos (2 * α) = 2 * cos (5 * α / 2) * cos (α / 2) := by
    have h4 : cos (3 * α) + cos (2 * α) = 2 * cos (5 * α / 2) * cos (α / 2) := by
      have h5 : cos (3 * α) = cos ((5 * α / 2 + α / 2)) := by ring_nf
      have h6 : cos (2 * α) = cos ((5 * α / 2 - α / 2)) := by ring_nf
      rw [h5, h6]
      rw [cos_add, cos_sub]
      ring
    linarith

  calc
    cos α + cos (2 * α) + cos (6 * α) + cos (7 * α)
        = (cos α + cos (7 * α)) + (cos (2 * α) + cos (6 * α)) := by ring
    _ = 2 * cos (4 * α) * cos (3 * α) + 2 * cos (4 * α) * cos (2 * α) := by rw [h1, h2]
    _ = 2 * cos (4 * α) * (cos (3 * α) + cos (2 * α)) := by ring
    _ = 2 * cos (4 * α) * (2 * cos (5 * α / 2) * cos (α / 2)) := by rw [h3]
    _ = 4 * cos (α / 2) * cos (5 * α / 2) * cos (4 * α) := by ring