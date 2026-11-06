import Mathlib

open Real Set
open scoped Real

theorem algebra_189159 (α : ℝ) :
  (cos α)^2 + (cos (2/3 * π + α))^2 + (cos (2/3 * π - α))^2 = 3/2 := by
  have h3 : cos (2/3 * π) = -1/2 := by
    have h2 : 2/3 * π = π - π/3 := by
      ring_nf
    rw [h2]
    rw [cos_pi_sub]
    have h3 : cos (π / 3) = 1 / 2 := by
      exact cos_pi_div_three
    linarith [h3]
  
  have h4 : sin (2/3 * π) = Real.sqrt 3 / 2 := by
    have h5 : 2/3 * π = π - π/3 := by
      ring_nf
    rw [h5]
    rw [sin_pi_sub]
    have h6 : sin (π / 3) = Real.sqrt 3 / 2 := by
      exact sin_pi_div_three
    linarith [h6]

  have h5 : cos (2/3 * π + α) = cos (2/3 * π) * cos α - sin (2/3 * π) * sin α := by
    rw [cos_add]

  have h6 : cos (2/3 * π - α) = cos (2/3 * π) * cos α + sin (2/3 * π) * sin α := by
    rw [cos_sub]

  rw [h5, h6]
  rw [h3, h4]

  -- Now we need to show that the expression becomes 3/2
  have h7 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h8 : Real.sqrt 3 ^ 2 = 3 := by
    exact Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  nlinarith [Real.sqrt_nonneg 3, h7, h8, sq_nonneg (sin α), sq_nonneg (cos α), sq_nonneg (sin α * Real.sqrt 3 / 2), sq_nonneg (cos α * Real.sqrt 3 / 2)]