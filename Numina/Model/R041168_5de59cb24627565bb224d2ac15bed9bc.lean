import Mathlib

theorem algebra_313204 (α : ℝ) : Real.cos α + Real.cos (3 * α) + Real.cos (5 * α) + Real.cos (7 * α) =
    4 * Real.cos α * Real.cos (2 * α) * Real.cos (4 * α) := by
  have h1 : Real.cos (5 * α) + Real.cos (3 * α) = 2 * Real.cos (4 * α) * Real.cos α := by
    have h11 : Real.cos (5 * α) = Real.cos (4 * α + α) := by ring_nf
    have h22 : Real.cos (3 * α) = Real.cos (4 * α - α) := by ring_nf
    rw [h11, h22]
    have h33 : Real.cos (4 * α + α) = Real.cos (4 * α) * Real.cos α - Real.sin (4 * α) * Real.sin α := by
      rw [Real.cos_add]
    have h44 : Real.cos (4 * α - α) = Real.cos (4 * α) * Real.cos α + Real.sin (4 * α) * Real.sin α := by
      rw [Real.cos_sub]
    rw [h33, h44]
    ring
  have h2 : Real.cos (7 * α) + Real.cos α = 2 * Real.cos (4 * α) * Real.cos (3 * α) := by
    have h11 : Real.cos (7 * α) = Real.cos (4 * α + 3 * α) := by ring_nf
    have h22 : Real.cos α = Real.cos (4 * α - 3 * α) := by ring_nf
    rw [h11, h22]
    have h33 : Real.cos (4 * α + 3 * α) = Real.cos (4 * α) * Real.cos (3 * α) - Real.sin (4 * α) * Real.sin (3 * α) := by
      rw [Real.cos_add]
    have h44 : Real.cos (4 * α - 3 * α) = Real.cos (4 * α) * Real.cos (3 * α) + Real.sin (4 * α) * Real.sin (3 * α) := by
      rw [Real.cos_sub]
    rw [h33, h44]
    ring
  have h3 : Real.cos (3 * α) + Real.cos α = 2 * Real.cos (2 * α) * Real.cos α := by
    have h4 : Real.cos (3 * α) = 4 * Real.cos α ^ 3 - 3 * Real.cos α := by
      rw [Real.cos_three_mul]
    have h5 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by
      rw [Real.cos_two_mul]
    rw [h4, h5]
    have h8 : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by
      have h9 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      linarith
    nlinarith [sq_nonneg (Real.cos α), sq_nonneg (Real.sin α), Real.sin_sq_add_cos_sq α, sq_nonneg (Real.cos α ^ 2 - 1)]
  calc
    Real.cos α + Real.cos (3 * α) + Real.cos (5 * α) + Real.cos (7 * α)
        = (Real.cos (7 * α) + Real.cos α) + (Real.cos (5 * α) + Real.cos (3 * α)) := by ring
    _ = (2 * Real.cos (4 * α) * Real.cos (3 * α)) + (2 * Real.cos (4 * α) * Real.cos α) := by 
      rw [h2, h1]
    _ = 2 * Real.cos (4 * α) * (Real.cos (3 * α) + Real.cos α) := by ring
    _ = 2 * Real.cos (4 * α) * (2 * Real.cos (2 * α) * Real.cos α) := by 
      rw [h3]
    _ = 4 * Real.cos α * Real.cos (2 * α) * Real.cos (4 * α) := by 
      ring