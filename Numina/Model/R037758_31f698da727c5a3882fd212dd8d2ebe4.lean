import Mathlib

open Real Set
open scoped Real

theorem algebra_178530 (α : Real) :
  sin (4 * α) - sin (5 * α) - sin (6 * α) + sin (7 * α) =
  -4 * sin (α / 2) * sin α * sin (11 * α / 2) := by
  have h1 : sin (4 * α) - sin (5 * α) - sin (6 * α) + sin (7 * α) =
    (sin (4 * α) + sin (7 * α)) - (sin (5 * α) + sin (6 * α)) := by ring
  rw [h1]
  have h2 : sin (4 * α) + sin (7 * α) = 2 * sin (11 * α / 2) * cos (3 * α / 2) := by
    rw [show 4 * α = 11 * α / 2 - 3 * α / 2 by ring]
    rw [show 7 * α = 11 * α / 2 + 3 * α / 2 by ring]
    rw [sin_sub, sin_add]
    ring
  have h3 : sin (5 * α) + sin (6 * α) = 2 * sin (11 * α / 2) * cos (α / 2) := by
    rw [show 5 * α = 11 * α / 2 - α / 2 by ring]
    rw [show 6 * α = 11 * α / 2 + α / 2 by ring]
    rw [sin_sub, sin_add]
    ring
  rw [h2, h3]
  have h4 : cos (3 * α / 2) - cos (α / 2) = -2 * sin α * sin (α / 2) := by
    have h5 : cos (3 * α / 2) - cos (α / 2) =
      -2 * sin ((3 * α / 2 + α / 2) / 2) * sin ((3 * α / 2 - α / 2) / 2) := by
      rw [cos_sub_cos]
      <;> ring
    rw [h5]
    have h6 : (3 * α / 2 + α / 2) / 2 = α := by ring
    have h7 : (3 * α / 2 - α / 2) / 2 = α / 2 := by ring
    rw [h6, h7]
  have h5 : 2 * sin (11 * α / 2) * cos (3 * α / 2) - 2 * sin (11 * α / 2) * cos (α / 2) =
    2 * sin (11 * α / 2) * (cos (3 * α / 2) - cos (α / 2)) := by ring
  rw [h5, h4]
  ring