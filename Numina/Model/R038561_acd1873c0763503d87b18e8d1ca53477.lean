import Mathlib

theorem algebra_231525 (α β : ℝ) : Real.sin (α + β) * Real.sin (α - β) -
    (Real.sin α + Real.sin β) * (Real.sin α - Real.sin β) = 0 := by
  have h1 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := Real.sin_add α β
  have h2 : Real.sin (α - β) = Real.sin α * Real.cos β - Real.cos α * Real.sin β := Real.sin_sub α β
  rw [h1, h2]
  have h3 : (Real.sin α * Real.cos β + Real.cos α * Real.sin β) * (Real.sin α * Real.cos β - Real.cos α * Real.sin β) =
           (Real.sin α * Real.cos β) ^ 2 - (Real.cos α * Real.sin β) ^ 2 := by ring
  have h4 : (Real.sin α + Real.sin β) * (Real.sin α - Real.sin β) = (Real.sin α) ^ 2 - (Real.sin β) ^ 2 := by ring
  rw [h3, h4]
  have h6 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  have h7 : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
  nlinarith [Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β, 
            sq_nonneg (Real.sin α * Real.sin β), sq_nonneg (Real.cos α * Real.cos β),
            sq_nonneg (Real.sin α * Real.cos β - Real.sin β * Real.cos α),
            sq_nonneg (Real.sin α ^ 2 - Real.sin β ^ 2)
          ]