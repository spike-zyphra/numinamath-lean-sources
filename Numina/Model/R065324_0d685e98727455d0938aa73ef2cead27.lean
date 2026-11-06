import Mathlib

open Real Set
open scoped Real

theorem algebra_185504 (α : ℝ) :
  (sin α)^6 + (cos α)^6 + 3 * (sin α)^2 * (cos α)^2 = 1 := by 
  have h1 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h2 : sin α ^ 4 + cos α ^ 4 = 1 - 2 * sin α ^ 2 * cos α ^ 2 := by
    have h4 : sin α ^ 4 + cos α ^ 4 = (sin α ^ 2 + cos α ^ 2) ^ 2 - 2 * sin α ^ 2 * cos α ^ 2 := by
      ring
    rw [h4]
    rw [h1]
    <;> ring
  have h3 : sin α ^ 6 + cos α ^ 6 = 1 - 3 * sin α ^ 2 * cos α ^ 2 := by 
    have h4 : sin α ^ 6 + cos α ^ 6 = (sin α ^ 2 + cos α ^ 2) ^ 3 - 3 * sin α ^ 2 * cos α ^ 2 * (sin α ^ 2 + cos α ^ 2) := by 
      ring
    rw [h4]
    rw [h1]
    <;> ring
  nlinarith [h1, h3]