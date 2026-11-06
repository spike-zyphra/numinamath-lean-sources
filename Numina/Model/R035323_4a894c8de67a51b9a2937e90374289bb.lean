import Mathlib

open Real Set
open scoped Real

theorem algebra_162491 (α β : Real) :
  (sin α - sin β) * (sin α + sin β) = sin (α - β) * sin (α + β) := by
  have h1 : sin (α - β) = sin α * cos β - cos α * sin β := by
    rw [sin_sub]
  have h2 : sin (α + β) = sin α * cos β + cos α * sin β := by
    rw [sin_add]
  rw [h1, h2]
  have h3 : sin α ^ 2 + cos α ^ 2 = 1 := by
    exact sin_sq_add_cos_sq α
  have h4 : sin β ^ 2 + cos β ^ 2 = 1 := by
    exact sin_sq_add_cos_sq β
  have eq1 : (sin α - sin β) * (sin α + sin β) = sin α ^ 2 - sin β ^ 2 := by
    ring
  have eq2 : (sin α * cos β - cos α * sin β) * (sin α * cos β + cos α * sin β) =
      sin α ^ 2 * cos β ^ 2 - cos α ^ 2 * sin β ^ 2 := by
    ring_nf
  rw [eq1, eq2]
  have h5 : cos α ^ 2 = 1 - sin α ^ 2 := by 
    linarith 
  have h6 : cos β ^ 2 = 1 - sin β ^ 2 := by
    linarith
  rw [h5, h6]
  nlinarith