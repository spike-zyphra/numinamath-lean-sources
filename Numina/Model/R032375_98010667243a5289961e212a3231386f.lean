import Mathlib

open Real Set
open scoped Real

theorem algebra_163576 (α β : ℝ) :
  (cos (α - 2 * β))^2 - (cos (α - π / 2))^2 - (cos (2 * β - π))^2 =
  2 * sin α * sin (2 * β - α) * cos (2 * β) := by
  have h1 : cos (α - π / 2) = sin α := by
    have h2 : cos (α - π / 2) = sin α := by
      rw [cos_sub_pi_div_two]
    exact h2
  have h2 : cos (2 * β - π) = -cos (2 * β) := by
    have h3 : cos (2 * β - π) = -cos (2 * β) := by
      have h4 : cos (2 * β - π) = cos (2 * β) * cos π + sin (2 * β) * sin π := by
        rw [cos_sub]
      rw [h4]
      have h5 : cos π = -1 := by
        exact cos_pi
      have h6 : sin π = 0 := by
        exact sin_pi
      rw [h5, h6]
      all_goals
        ring
    exact h3
  have h3 : cos (α - 2 * β) = cos α * cos (2 * β) + sin α * sin (2 * β) := by
    rw [cos_sub]
  have h4 : sin (2 * β - α) = sin (2 * β) * cos α - cos (2 * β) * sin α := by
    rw [sin_sub]
  rw [h1, h2, h3, h4]
  have h5 : cos (2 * β) ^ 2 + sin (2 * β) ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq (2 * β)
  have h6 : sin α ^ 2 + cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq (2 * β), 
    Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq (2 * β), 
    sq_nonneg (cos α - sin α), sq_nonneg (cos (2 * β) - sin (2 * β)), 
    sq_nonneg (cos α - cos (2 * β)), sq_nonneg (sin α - sin (2 * β)), 
    sq_nonneg (cos α * sin (2 * β) - sin α * cos (2 * β)), sq_nonneg (sin α * cos α), sq_nonneg (sin (2 * β) * cos (2 * β))
  ]