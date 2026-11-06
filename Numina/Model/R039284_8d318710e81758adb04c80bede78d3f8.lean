import Mathlib

open Real Set
open scoped Real

theorem algebra_185545 (α β : ℝ) :
  sin α ^ 2 - sin β ^ 2 = sin (α + β) * sin (α - β) := by
  have h1 : sin (α + β) = sin α * cos β + cos α * sin β := by
    rw [sin_add]
  have h2 : sin (α - β) = sin α * cos β - cos α * sin β := by 
    rw [sin_sub]
  rw [h1, h2]
  have h3 : (sin α * cos β + cos α * sin β) * (sin α * cos β - cos α * sin β) = (sin α * cos β) ^ 2 - (cos α * sin β) ^ 2 := by ring
  rw [h3]
  have h4 : (sin α * cos β) ^ 2 - (cos α * sin β) ^ 2 = 
    sin α ^ 2 * (cos β ^ 2) - (cos α ^ 2) * (sin β ^ 2) := by ring
  rw [h4]
  have h5 : cos β ^ 2 = 1 - sin β ^ 2 := by 
    rw [cos_sq']
  have h6 : cos α ^ 2 = 1 - sin α ^ 2 := by
    rw [cos_sq']
  rw [h5, h6]
  ring