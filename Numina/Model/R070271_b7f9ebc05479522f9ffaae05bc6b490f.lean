import Mathlib

theorem algebra_186092 (α : Real) : 3 + 4 * Real.cos (4 * α) + Real.cos (8 * α) = 8 * (Real.cos (2 * α))^4 := by
  have h1 : Real.cos (4 * α) = 2 * Real.cos (2 * α)^2 - 1 := by 
    rw [show 4 * α = 2 * (2 * α) by ring]
    exact Real.cos_two_mul (2 * α)
  
  have h2 : Real.cos (8 * α) = 2 * Real.cos (4 * α)^2 - 1 := by 
    rw [show 8 * α = 2 * (4 * α) by ring]
    exact Real.cos_two_mul (4 * α)
  
  rw [h1] at h2
  
  -- Now h2 is Real.cos (8 * α) = 2 * (2 * Real.cos (2 * α)^2 - 1)^2 - 1
  
  rw [h1, h2]
  
  -- Now we need to expand the expression 3 + 4 * (2 * Real.cos (2 * α)^2 - 1) + (2 * (2 * Real.cos (2 * α)^2 - 1)^2 - 1)
  
  -- Let's expand (2 * Real.cos (2 * α)^2 - 1)^2
  -- (2x - 1)^2 = 4x^2 - 4x + 1
  -- Multiply by 2: 8x^2 - 8x + 2
  -- Then subtract 1: 8x^2 - 8x + 1
  
  -- So 3 + 4*(2x^2 - 1) + (8x^2 - 8x + 1) = 3 + 8x^2 - 4 + 8x^2 - 8x + 1
  -- Combine constants: 3 - 4 + 1 = 0
  -- Combine x terms: 8x^2 - 8x^2 = 0
  -- Remaining term: 8x^4
  
  -- Let x = Real.cos (2 * α)
  
  nlinarith [sq_nonneg (Real.cos (2 * α) - 1), sq_nonneg (Real.cos (2 * α) + 1)]