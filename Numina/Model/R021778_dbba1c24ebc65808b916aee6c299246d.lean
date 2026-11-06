import Mathlib

theorem algebra_282825 (α β : ℝ) : Real.sin α * Real.sin (α + β) + Real.cos α * Real.cos (α + β) = Real.cos β := by
  have h1 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by
    rw [Real.sin_add]
  have h2 : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := by 
    rw [Real.cos_add]
  rw [h1, h2]
  have h3 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have eq1 : Real.sin α * (Real.sin α * Real.cos β + Real.cos α * Real.sin β) + Real.cos α * (Real.cos α * Real.cos β - Real.sin α * Real.sin β) = Real.cos β * (Real.sin α ^ 2 + Real.cos α ^ 2) := by
    ring_nf
  rw [eq1]
  rw [h3]
  all_goals norm_num