import Mathlib

open Real Set
open scoped Real

theorem algebra_163333 (α β : ℝ) :
  (cos α) ^ 2 + (cos β) ^ 2 - 2 * cos α * cos β * cos (α - β) =
  (sin (α - β)) ^ 2 := by
  have h1 : cos (α - β) = cos α * cos β + sin α * sin β := by
    rw [cos_sub]
  have h2 : sin (α - β) = sin α * cos β - cos α * sin β := by 
    rw [sin_sub]
  rw [h1, h2]
  have h3 : sin α ^ 2 + cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α
  have h4 : sin β ^ 2 + cos β ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq β
  nlinarith [sq_nonneg (sin α * cos β - cos α * sin β), sq_nonneg (cos α - cos β), sq_nonneg (sin α - sin β), Real.sin_le_one α, Real.sin_le_one β, Real.sin_le_one (α - β), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq (α - β)]