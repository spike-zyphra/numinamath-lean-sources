import Mathlib

open Real Set
open scoped Real

theorem inequalities_600177 (α : ℝ) :
  (sin α)^10 + (cos α)^10 ≥ 1/16 := by
  have h1 : sin α ^ 2 + cos α ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq α
  have h2 : (sin α) ^ 10 = (sin α ^ 2) ^ 5 := by ring
  have h3 : (cos α) ^ 10 = (cos α ^ 2) ^ 5 := by ring
  rw [h2, h3]
  have h4 : cos α ^ 2 = 1 - sin α ^ 2 := by
    have h5 : sin α ^ 2 + cos α ^ 2 = 1 := by 
      linarith [Real.sin_sq_add_cos_sq α]
    linarith
  have h51 : (cos α ^ 2) ^ 5 = (1 - sin α ^ 2) ^ 5 := by
    rw [h4]
  rw [h51]
  have h11 : sin α ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (sin α), sq_nonneg (cos α), Real.sin_sq_add_cos_sq α]
  have h12 : sin α ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (sin α), sq_nonneg (cos α), Real.sin_sq_add_cos_sq α]
  nlinarith [sq_nonneg ((sin α ^ 2) - 1 / 2), sq_nonneg ((sin α ^ 2) ^ 2 - 1 / 4), sq_nonneg ((sin α ^ 2) ^ 3 - (1 / 8)), sq_nonneg ((sin α ^ 2) ^ 2 - (1 - sin α ^ 2) ^ 2), sq_nonneg ((sin α ^ 2) - (1 - sin α ^ 2)), sq_nonneg ((sin α ^ 2) ^ 2 - (1 - sin α ^ 2) ^ 2)]