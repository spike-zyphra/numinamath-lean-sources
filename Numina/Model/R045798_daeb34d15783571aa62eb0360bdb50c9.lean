import Mathlib

open Real Set
open scoped Real

theorem algebra_162990 (α : ℝ) :
  (cos (α - π / 2))^6 + (sin (α - 3 * π / 2))^6 -
  (3 / 4) * ((sin (α + π / 2))^2 - (cos (α + 3 * π / 2))^2)^2 = 1 / 4 := by
  have h1 : cos (α - π / 2) = sin α := by 
    rw [cos_sub, cos_pi_div_two, sin_pi_div_two]
    ring
  have h2 : sin (α - 3 * π / 2) = cos α := by
    have h3 : α - 3 * π / 2 = (α + π / 2) - 2 * π := by 
      linarith
    rw [h3]
    have h4 : sin ((α + π / 2) - 2 * π) = sin (α + π / 2) := by 
      rw [show (α + π / 2) - 2 * π = (α + π / 2) - (2 * π) by ring]
      have h5 : sin ((α + π / 2) - (2 * π)) = sin (α + π / 2) := by 
        rw [sin_sub, sin_two_pi, cos_two_pi]
        simp
      exact h5
    rw [h4]
    have h5 : sin (α + π / 2) = cos α := by
      rw [sin_add, sin_pi_div_two, cos_pi_div_two]
      ring
    rw [h5]
  have h3 : sin (α + π / 2) = cos α := by 
    rw [sin_add, sin_pi_div_two, cos_pi_div_two]
    ring
  have h4 : cos (α + 3 * π / 2) = sin α := by 
    have h5 : α + 3 * π / 2 = (α + π) + π / 2 := by 
      ring
    rw [h5]
    have h6 : cos ((α + π) + π / 2) = -sin (α + π) := by
      rw [cos_add, cos_pi_div_two, sin_pi_div_two]
      all_goals ring
    rw [h6]
    have h7 : sin (α + π) = -sin α := by 
      rw [sin_add, sin_pi, cos_pi]
      ring
    rw [h7]
    all_goals ring
  rw [h1, h2, h3, h4]
  have h5 : sin α ^ 2 + cos α ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq α
  have eq1 : sin α ^ 6 + cos α ^ 6 = 1 - 3 * (sin α ^ 2 * cos α ^ 2) := by 
    have h6 : sin α ^ 2 + cos α ^ 2 = 1 := h5
    have eq2 : sin α ^ 6 + cos α ^ 6 = (sin α ^ 2) ^ 3 + (cos α ^ 2) ^ 3 := by 
      ring_nf
    rw [eq2]
    have eq3 : (sin α ^ 2) ^ 3 + (cos α ^ 2) ^ 3 = (sin α ^ 2 + cos α ^ 2) ^ 3 - 3 * (sin α ^ 2 * cos α ^ 2) * (sin α ^ 2 + cos α ^ 2) := by
      ring_nf
    rw [eq3, h6]
    all_goals norm_num [h6]
  have eq2 : (cos α ^ 2 - sin α ^ 2) ^ 2 = (1 - 4 * (sin α ^ 2 * cos α ^ 2)) := by 
    have h6 : sin α ^ 2 + cos α ^ 2 = 1 := h5
    have eq3 : (cos α ^ 2 - sin α ^ 2) ^ 2 = (cos α ^ 2) ^ 2 - 2 * (sin α ^ 2 * cos α ^ 2) + (sin α ^ 2) ^ 2 := by
      ring_nf
    have eq4 : (cos α ^ 2) ^ 2 + (sin α ^ 2) ^ 2 = 1 - 2 * (sin α ^ 2 * cos α ^ 2) := by 
      have h7 : (cos α ^ 2) ^ 2 + (sin α ^ 2) ^ 2 = (sin α ^ 2 + cos α ^ 2) ^ 2 - 2 * (sin α ^ 2 * cos α ^ 2) := by 
        ring_nf
      rw [h7, h6]
      all_goals norm_num [h6]
    linarith [eq3, eq4]
  nlinarith [sq_nonneg (sin α ^ 2 - cos α ^ 2), sq_nonneg (sin α * cos α), sq_nonneg (sin α ^ 2 + cos α ^ 2 - 1)]