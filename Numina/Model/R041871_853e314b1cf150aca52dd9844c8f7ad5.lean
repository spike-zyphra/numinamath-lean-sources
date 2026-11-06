import Mathlib

theorem algebra_186066 (α : ℝ) :
    Real.sin (5 * α) - Real.sin (6 * α) - Real.sin (7 * α) + Real.sin (8 * α) =
    -4 * Real.sin (α / 2) * Real.sin α * Real.sin (13 * α / 2) := by 
  have h1 : Real.sin (5 * α) - Real.sin (6 * α) = -2 * Real.cos (11 * α / 2) * Real.sin (α / 2) := by 
    have h2 : Real.sin (5 * α) - Real.sin (6 * α) = 2 * Real.cos ((5 * α + 6 * α) / 2) * Real.sin ((5 * α - 6 * α) / 2) := by 
      rw [show 5 * α = (5 * α + 6 * α) / 2 + (5 * α - 6 * α) / 2 by ring]
      rw [show 6 * α = (5 * α + 6 * α) / 2 - (5 * α - 6 * α) / 2 by ring]
      rw [Real.sin_add, Real.sin_sub]
      ring
    have h3 : (5 * α + 6 * α) / 2 = 11 * α / 2 := by ring 
    have h4 : (5 * α - 6 * α) / 2 = - (α / 2) := by ring 
    rw [h3, h4] at h2 
    have h5 : Real.sin (- (α / 2)) = - Real.sin (α / 2) := by 
      rw [Real.sin_neg]
    rw [h5] at h2
    linarith 
  have h2' : Real.sin (7 * α) - Real.sin (8 * α) = -2 * Real.cos (15 * α / 2) * Real.sin (α / 2) := by 
    have h3 : Real.sin (7 * α) - Real.sin (8 * α) = 2 * Real.cos ((7 * α + 8 * α) / 2) * Real.sin ((7 * α - 8 * α) / 2) := by 
      rw [show 7 * α = (7 * α + 8 * α) / 2 + (7 * α - 8 * α) / 2 by ring]
      rw [show 8 * α = (7 * α + 8 * α) / 2 - (7 * α - 8 * α) / 2 by ring]
      rw [Real.sin_add, Real.sin_sub]
      ring
    have h4 : (7 * α + 8 * α) / 2 = 15 * α / 2 := by ring 
    have h5 : (7 * α - 8 * α) / 2 = - (α / 2) := by ring 
    rw [h4, h5] at h3 
    have h6 : Real.sin (- (α / 2)) = - Real.sin (α / 2) := by 
      rw [Real.sin_neg]
    rw [h6] at h3 
    linarith
  calc
    Real.sin (5 * α) - Real.sin (6 * α) - Real.sin (7 * α) + Real.sin (8 * α)
        = (Real.sin (5 * α) - Real.sin (6 * α)) - (Real.sin (7 * α) - Real.sin (8 * α)) := by ring
    _ = (-2 * Real.cos (11 * α / 2) * Real.sin (α / 2)) - (-2 * Real.cos (15 * α / 2) * Real.sin (α / 2)) := by
      rw [h1, h2']
    _ = -2 * Real.sin (α / 2) * (Real.cos (11 * α / 2) - Real.cos (15 * α / 2)) := by 
      ring 
    _ = -2 * Real.sin (α / 2) * (2 * Real.sin (13 * α / 2) * Real.sin α) := by 
      have h3 : Real.cos (11 * α / 2) - Real.cos (15 * α / 2) = 2 * Real.sin (13 * α / 2) * Real.sin α := by 
        have h4 : Real.cos (11 * α / 2) - Real.cos (15 * α / 2) = -2 * Real.sin ((11 * α / 2 + 15 * α / 2) / 2) * Real.sin ((11 * α / 2 - 15 * α / 2) / 2) := by 
          rw [Real.cos_sub_cos]
          <;> ring_nf 
        have h5 : (11 * α / 2 + 15 * α / 2) / 2 = 13 * α / 2 := by ring_nf
        have h6 : (11 * α / 2 - 15 * α / 2) / 2 = - α := by ring_nf
        have h7 : Real.sin (- α) = - Real.sin α := by 
          rw [show -α = -α by ring]
          simp [Real.sin_neg]
        rw [h5, h6] at h4 
        have h8 : -2 * Real.sin (13 * α / 2) * Real.sin (- α) = 2 * Real.sin (13 * α / 2) * Real.sin α := by
          rw [h7]
          ring 
        linarith [h4, h8] 
      rw [h3]
      all_goals ring
    _ = -4 * Real.sin (α / 2) * Real.sin α * Real.sin (13 * α / 2) := by 
      ring