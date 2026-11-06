import Mathlib

theorem algebra_185246 (α : ℝ) :
    Real.cos (2 * α) - Real.cos (3 * α) - Real.cos (4 * α) + Real.cos (5 * α) =
    -4 * Real.sin (α / 2) * Real.sin α * Real.cos (7 * α / 2) := by

  have h1 : Real.cos (2 * α) - Real.cos (3 * α) = 2 * Real.sin (5 * α / 2) * Real.sin (α / 2) := by 
    rw [show 2 * α = 5 * α / 2 + ( - (α / 2) ) by ring]
    rw [show 3 * α = 5 * α / 2 - ( - (α / 2) ) by ring]
    rw [Real.cos_add, Real.cos_sub]
    have h5 : Real.sin ( - (α / 2) ) = - Real.sin (α / 2) := by 
      rw [show - (α / 2) = - (α / 2) by ring]
      simp [Real.sin_neg]
    have h6 : Real.cos (- (α / 2)) = Real.cos (α / 2) := by 
      rw [show - (α / 2) = - (α / 2) by ring]
      simp [Real.cos_neg]
    rw [h5, h6]
    ring_nf

  have h2 : Real.cos (5 * α) - Real.cos (4 * α) = -2 * Real.sin (9 * α / 2) * Real.sin (α / 2) := by 
    have h8 : Real.cos (5 * α) - Real.cos (4 * α) = -2 * Real.sin ( (5 * α + 4 * α) / 2 ) * Real.sin ( (5 * α - 4 * α) / 2 ) := by 
      have h9 : Real.cos (5 * α) - Real.cos (4 * α) = -2 * Real.sin ( (5 * α + 4 * α) / 2 ) * Real.sin ( (5 * α - 4 * α) / 2 ) := by 
        have h10 : Real.cos (5 * α) = Real.cos ( ( (5 * α + 4 * α) / 2 + (5 * α - 4 * α) / 2 ) ) := by ring_nf
        have h11 : Real.cos (4 * α) = Real.cos ( ( (5 * α + 4 * α) / 2 - (5 * α - 4 * α) / 2 ) ) := by ring_nf
        rw [h10, h11]
        rw [Real.cos_add, Real.cos_sub]
        <;> ring_nf 
      linarith
    have h9 : (5 * α + 4 * α) / 2 = 9 * α / 2 := by ring 
    have h10 : (5 * α - 4 * α) / 2 = α / 2 := by ring 
    rw [h9, h10] at h8 
    linarith [h8] 

  calc 
    Real.cos (2 * α) - Real.cos (3 * α) - Real.cos (4 * α) + Real.cos (5 * α)
        = (Real.cos (2 * α) - Real.cos (3 * α)) + (Real.cos (5 * α) - Real.cos (4 * α)) := by ring
    _ = 2 * Real.sin (5 * α / 2) * Real.sin (α / 2) + (-2 * Real.sin (9 * α / 2) * Real.sin (α / 2)) := by 
      rw [h1, h2]
    _ = 2 * Real.sin (α / 2) * (Real.sin (5 * α / 2) - Real.sin (9 * α / 2)) := by 
      ring
    _ = 2 * Real.sin (α / 2) * (-2 * Real.cos (7 * α / 2) * Real.sin α) := by 
      have h3 : Real.sin (5 * α / 2) - Real.sin (9 * α / 2) = -2 * Real.cos (7 * α / 2) * Real.sin α := by 
        have h4 : Real.sin (5 * α / 2) - Real.sin (9 * α / 2) = 2 * Real.cos ( (5 * α / 2 + 9 * α / 2) / 2 ) * Real.sin ( (5 * α / 2 - 9 * α / 2) / 2 ) := by 
          rw [show (5 * α / 2) = (5 * α / 2 + 9 * α / 2) / 2 + (5 * α / 2 - 9 * α / 2) / 2 by ring]
          rw [show (9 * α / 2) = (5 * α / 2 + 9 * α / 2) / 2 - (5 * α / 2 - 9 * α / 2) / 2 by ring]
          rw [Real.sin_add, Real.sin_sub]
          ring_nf
        have h5 : (5 * α / 2 + 9 * α / 2) / 2 = 7 * α / 2 := by ring 
        have h6 : (5 * α / 2 - 9 * α / 2) / 2 = - α := by ring 
        rw [h5, h6] at h4 
        have h7 : Real.sin (- α) = - Real.sin α := by 
          rw [show -α = -α by ring]
          simp [Real.sin_neg]
        rw [h7] at h4 
        linarith
      rw [h3]
      all_goals ring
    _ = -4 * Real.sin (α / 2) * Real.sin α * Real.cos (7 * α / 2) := by 
      ring