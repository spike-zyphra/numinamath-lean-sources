import Mathlib

theorem algebra_233281 (α β : ℝ) (h : Real.cos α ^ 2 - Real.cos β ^ 2 = m) :
    Real.sin (α + β) * Real.sin (α - β) = -m := by
  have h1 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by 
    rw [Real.sin_add]
  have h2 : Real.sin (α - β) = Real.sin α * Real.cos β - Real.cos α * Real.sin β := by 
    rw [Real.sin_sub]
  rw [h1, h2]
  have h3 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h4 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  have h5 : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by linarith 
  have h6 : Real.sin β ^ 2 = 1 - Real.cos β ^ 2 := by linarith 
  have eq1 : (Real.sin α * Real.cos β + Real.cos α * Real.sin β) * (Real.sin α * Real.cos β - Real.cos α * Real.sin β) =
          (Real.sin α ^ 2) * (Real.cos β ^ 2) - (Real.cos α ^ 2) * (Real.sin β ^ 2) := by 
    ring
  rw [eq1]
  rw [h5, h6]
  have eq2 : (1 - Real.cos α ^ 2) * Real.cos β ^ 2 - Real.cos α ^ 2 * (1 - Real.cos β ^ 2) =
          Real.cos β ^ 2 - Real.cos α ^ 2 := by
    ring
  rw [eq2]
  linarith