import Mathlib

theorem algebra_178966 (α β : ℝ) : 1 - Real.sin α ^ 2 - Real.sin β ^ 2 + 2 * Real.sin α * Real.sin β * Real.cos (α - β) = Real.cos (α - β) ^ 2 := by
  have h : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by
    rw [Real.cos_sub]
  rw [h]
  have h1 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  have h2 : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
          sq_nonneg (Real.cos α * Real.sin β - Real.sin α * Real.cos β),
          sq_nonneg (Real.cos α * Real.cos β - Real.sin α * Real.sin β)
        ]