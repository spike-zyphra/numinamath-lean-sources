import Mathlib

open Real Set
open scoped Real

theorem algebra_185408 (α β : ℝ) :
  (cos α - cos β)^2 - (sin α - sin β)^2 = -4 * (sin ((α - β) / 2))^2 * cos (α + β) := by
  have h2 : cos α - cos β = -2 * sin ((α + β) / 2) * sin ((α - β) / 2) := by
    rw [show (α : ℝ) = (α + β) / 2 + (α - β) / 2 by ring]
    rw [show (β : ℝ) = (α + β) / 2 - (α - β) / 2 by ring]
    rw [cos_add, cos_sub]
    ring
  have h3 : sin α - sin β = 2 * cos ((α + β) / 2) * sin ((α - β) / 2) := by
    rw [show (α : ℝ) = (α + β) / 2 + (α - β) / 2 by ring]
    rw [show (β : ℝ) = (α + β) / 2 - (α - β) / 2 by ring]
    rw [sin_add, sin_sub]
    ring
  rw [h2, h3]
  have h4 : (-2 * sin ((α + β) / 2) * sin ((α - β) / 2)) ^ 2 - (2 * cos ((α + β) / 2) * sin ((α - β) / 2)) ^ 2 =
      4 * (sin ((α - β) / 2))^2 * (sin ((α + β) / 2)^2 - cos ((α + β) / 2)^2) := by
    ring_nf
  rw [h4]
  have h5 : sin ((α + β) / 2)^2 - cos ((α + β) / 2)^2 = - cos (α + β) := by 
    have hcos : cos (α + β) = 2 * cos ((α + β) / 2)^2 - 1 := by 
      rw [← cos_two_mul]
      ring_nf
    have hsin2 : sin ((α + β) / 2)^2 = 1 - cos ((α + β) / 2)^2 := by 
      linarith [sin_sq_add_cos_sq ((α + β) / 2)]
    rw [hcos, hsin2]
    ring
  rw [h5]
  all_goals ring