import Mathlib

theorem algebra_299160 (α β : ℝ) :
    Real.cos (α + β) ^ 2 + Real.cos (α - β) ^ 2 - Real.cos (2 * α) * Real.cos (2 * β) = 1 := by
  have h1 : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := Real.cos_add α β
  have h2 : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := Real.cos_sub α β
  have h3 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by 
    rw [Real.cos_two_mul]
  have h4 : Real.cos (2 * β) = 2 * Real.cos β ^ 2 - 1 := by 
    rw [Real.cos_two_mul]

  rw [h1, h2, h3, h4]

  nlinarith [Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β, 
          sq_nonneg (Real.sin α), sq_nonneg (Real.sin β), 
          sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.cos α - Real.cos β)]