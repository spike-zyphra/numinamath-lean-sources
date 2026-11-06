import Mathlib

open Real Set
open scoped Real

theorem algebra_185970 (α : ℝ) :
  3 - 4 * (cos ((3 / 2) * π - α))^2 =
  4 * cos (π / 6 + α) * cos (π / 6 - α) := by
  have h1 : cos ((3 / 2) * π - α) = - sin α := by
    have h2 : (3 / 2) * π - α = π + (π / 2 - α) := by
      ring
    rw [h2]
    rw [cos_add]
    rw [cos_pi, sin_pi]
    have h3 : cos (π / 2 - α) = sin α := by
      rw [cos_pi_div_two_sub]
    simp [h3]
    all_goals simp
    <;> ring
  
  have h4 : (cos ((3 / 2) * π - α))^2 = sin α ^ 2 := by
    rw [h1]
    ring

  rw [h4]

  have h5 : 4 * cos (π / 6 + α) * cos (π / 6 - α) = 4 * ( cos (π / 6) * cos α - sin (π / 6) * sin α ) * ( cos (π / 6) * cos α + sin (π / 6) * sin α ) := by
    rw [cos_add, cos_sub]
    all_goals ring

  rw [h5]

  have h6 : cos (π / 6) = Real.sqrt 3 / 2 := by
    exact cos_pi_div_six

  have h7 : sin (π / 6) = 1 / 2 := by
    exact sin_pi_div_six

  rw [h6, h7]

  have h8 : sin α ^ 2 = 1 - cos α ^ 2 := by
    have h9 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    linarith

  -- Convert sin^2 α into cos^2 α.

  have h9 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

  nlinarith [h8, Real.sin_sq_add_cos_sq α, h9]