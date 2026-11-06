import Mathlib

open Real Set
open scoped Real

theorem algebra_185350 (α β : ℝ) :
  (cos α - cos β)^2 + (sin α - sin β)^2 = 4 * (sin ((α - β) / 2))^2 := by
  have h1 : (cos α - cos β) ^ 2 + (sin α - sin β) ^ 2 =
    (cos α) ^ 2 - 2 * (cos α * cos β) + (cos β) ^ 2 + (sin α) ^ 2 - 2 * (sin α * sin β) + (sin β) ^ 2 := by
    ring
  rw [h1]
  have h2 : (cos α) ^ 2 + (sin α) ^ 2 = 1 := by 
    exact Real.cos_sq_add_sin_sq α
  have h3 : (cos β) ^ 2 + (sin β) ^ 2 = 1 := by 
    exact Real.cos_sq_add_sin_sq β
  have h4 : (cos α) ^ 2 - 2 * (cos α * cos β) + (cos β) ^ 2 + (sin α) ^ 2 - 2 * (sin α * sin β) + (sin β) ^ 2 =
      ((cos α) ^ 2 + (sin α) ^ 2) + ((cos β) ^ 2 + (sin β) ^ 2) - 2 * (cos α * cos β + sin α * sin β) := by
    ring
  rw [h4]
  rw [h2, h3]
  have h5 : cos α * cos β + sin α * sin β = cos (α - β) := by 
    rw [cos_sub]
  have h6 : (1 : ℝ) + (1 : ℝ) - 2 * (cos α * cos β + sin α * sin β) = 2 * (1 - cos (α - β)) := by 
    rw [show cos α * cos β + sin α * sin β = cos (α - β) by rw [cos_sub]]
    all_goals ring
  rw [h6]
  have h7 : 1 - cos (α - β) = 2 * (sin ((α - β) / 2)) ^ 2 := by
    have h8 : 1 - cos (α - β) = 2 * (sin ((α - β) / 2)) ^ 2 := by
      have h9 : sin ((α - β) / 2) ^ 2 = (1 - cos (α - β)) / 2 := by 
        rw [sin_sq_eq_half_sub]
        ring_nf
      nlinarith [h9]
    linarith [h8]
  rw [h7]
  <;> ring