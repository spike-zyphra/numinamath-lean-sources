import Mathlib

theorem algebra_185253 (α : ℝ) : Real.sin (4 * α) - Real.sin (5 * α) - Real.sin (6 * α) + Real.sin (7 * α) =
    -4 * Real.sin (α / 2) * Real.sin α * Real.sin (11 * α / 2) := by
  have h1 : Real.sin (4 * α) - Real.sin (5 * α) - Real.sin (6 * α) + Real.sin (7 * α) =
    (Real.sin (4 * α) + Real.sin (7 * α)) - (Real.sin (5 * α) + Real.sin (6 * α)) := by ring
  rw [h1]

  have h2 : Real.sin (4 * α) + Real.sin (7 * α) = 2 * Real.sin (11 * α / 2) * Real.cos (3 * α / 2) := by
    rw [show 4 * α = 11 * α / 2 - 3 * α / 2 by linarith, show 7 * α = 11 * α / 2 + 3 * α / 2 by linarith]
    rw [Real.sin_sub, Real.sin_add]
    ring

  have h3 : Real.sin (5 * α) + Real.sin (6 * α) = 2 * Real.sin (11 * α / 2) * Real.cos (α / 2) := by
    rw [show 5 * α = 11 * α / 2 - α / 2 by linarith, show 6 * α = 11 * α / 2 + α / 2 by linarith]
    rw [Real.sin_sub, Real.sin_add]
    ring

  rw [h2, h3]

  have h4 : 2 * Real.sin (11 * α / 2) * Real.cos (3 * α / 2) - 2 * Real.sin (11 * α / 2) * Real.cos (α / 2) =
          -4 * Real.sin (α / 2) * Real.sin α * Real.sin (11 * α / 2) := by
    have h5 : Real.cos (3 * α / 2) - Real.cos (α / 2) = -2 * Real.sin α * Real.sin (α / 2) := by
      have h51 : Real.cos (3 * α / 2) - Real.cos (α / 2) = -2 * Real.sin (( (3 * α / 2) + (α / 2) ) / 2) * Real.sin (( (3 * α / 2) - (α / 2) ) / 2) := by
        rw [Real.cos_sub_cos]
        <;> ring
      have h52 : ( (3 * α / 2) + (α / 2) ) / 2 = α := by linarith
      have h53 : ( (3 * α / 2) - (α / 2) ) / 2 = α / 2 := by linarith
      rw [h52, h53] at h51
      linarith

    have h6 : 2 * Real.sin (11 * α / 2) * Real.cos (3 * α / 2) - 2 * Real.sin (11 * α / 2) * Real.cos (α / 2) = 
      2 * Real.sin (11 * α / 2) * ( Real.cos (3 * α / 2) - Real.cos (α / 2) ) := by ring
    rw [h6]
    rw [h5]
    ring

  linarith [h4]