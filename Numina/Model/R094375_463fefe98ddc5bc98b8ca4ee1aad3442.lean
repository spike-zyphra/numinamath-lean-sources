import Mathlib

open Real Set
open scoped Real

theorem algebra_178559 (α β : ℝ) :
  (cos α - cos β)^2 + (sin α - sin β)^2 = 4 * (sin ((α - β) / 2))^2 := by
  have h1 : (cos α - cos β) ^ 2 + (sin α - sin β) ^ 2 =
    (cos α ^ 2 + sin α ^ 2) + (cos β ^ 2 + sin β ^ 2) - 2 * (cos α * cos β + sin α * sin β) := by 
    ring
  have h2 : cos α ^ 2 + sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  have h3 : cos β ^ 2 + sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
  rw [h1, h2, h3]
  have h4 : cos α * cos β + sin α * sin β = cos (α - β) := by 
    rw [Real.cos_sub]
  rw [h4]
  have h5 : 2 - 2 * cos (α - β) = 4 * (sin ((α - β) / 2)) ^ 2 := by
    have h6 : 1 - cos (α - β) = 2 * (sin ((α - β) / 2)) ^ 2 := by
      have h8 : sin ((α - β) / 2) ^ 2 = (1 - cos (α - β)) / 2 := by 
        have h9 : sin ((α - β) / 2) ^ 2 = (1 - cos (α - β)) / 2 := by 
          rw [Real.sin_sq_eq_half_sub]
          ring_nf
        linarith [h9]
      linarith [h8]
    linarith [h6]
  linarith [h5]