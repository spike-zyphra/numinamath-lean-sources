import Mathlib

open Real Set
open scoped Real

theorem algebra_158997 (α : ℝ) :
  cos α ^ 3 + cos (α + 2 * π / 3) ^ 3 + cos (α - 2 * π / 3) ^ 3 =
  3 / 4 * cos (3 * α) := by 
  have h1 : cos (α + 2 * π / 3) = cos α * cos (2 * π / 3) - sin α * sin (2 * π / 3) := by
    rw [cos_add]
  have h2 : cos (α - 2 * π / 3) = cos α * cos (2 * π / 3) + sin α * sin (2 * π / 3) := by
    rw [cos_sub]
  have h3 : cos (2 * π / 3) = -1 / 2 := by 
    have h1 : cos (2 * π / 3) = cos (π - π / 3) := by ring_nf
    rw [h1]
    rw [cos_pi_sub]
    all_goals norm_num
  have h4 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    have h1 : sin (2 * π / 3) = sin (π - π / 3) := by ring_nf
    rw [h1]
    rw [sin_pi_sub]
    have h2 : sin (π / 3) = Real.sqrt 3 / 2 := by 
      rw [sin_pi_div_three]
      all_goals norm_num
    linarith
  have eq1 : cos (α + 2 * π / 3) = -1 / 2 * cos α - Real.sqrt 3 / 2 * sin α := by
    rw [h1, h3, h4]
    all_goals ring
  have eq2 : cos (α - 2 * π / 3) = -1 / 2 * cos α + Real.sqrt 3 / 2 * sin α := by
    rw [h2, h3, h4]
    all_goals ring
  rw [eq1, eq2]
  have h7 : cos (3 * α) = 4 * cos α ^ 3 - 3 * cos α := by 
    rw [cos_three_mul]
  rw [h7]
  have h10 : cos α ^ 3 + (-1 / 2 * cos α - Real.sqrt 3 / 2 * sin α) ^ 3 + (-1 / 2 * cos α + Real.sqrt 3 / 2 * sin α) ^ 3 = 3 / 4 * (4 * cos α ^ 3 - 3 * cos α) := by 
    have h8 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have h100 : (-1 / 2 * cos α - Real.sqrt 3 / 2 * sin α) ^ 3 =
        -1/8 * cos α ^ 3 - 3 * Real.sqrt 3 / 8 * cos α ^ 2 * sin α - 9 / 8 * cos α * sin α ^ 2 - 3 * Real.sqrt 3 / 8 * sin α ^ 3 := by 
      ring_nf
      <;> simp [pow_three, h8, mul_add, add_mul, pow_two]
      <;> ring_nf
    have h110 : (-1 / 2 * cos α + Real.sqrt 3 / 2 * sin α) ^ 3 =
        -1/8 * cos α ^ 3 + 3 * Real.sqrt 3 / 8 * cos α ^ 2 * sin α - 9 / 8 * cos α * sin α ^ 2 + 3 * Real.sqrt 3 / 8 * sin α ^ 3 := by 
      ring_nf
      <;> simp [pow_three, h8, mul_add, add_mul, pow_two]
      <;> ring_nf
    calc
      cos α ^ 3 + (-1 / 2 * cos α - Real.sqrt 3 / 2 * sin α) ^ 3 + (-1 / 2 * cos α + Real.sqrt 3 / 2 * sin α) ^ 3 
          = cos α ^ 3 + (-1/8 * cos α ^ 3 - 3 * Real.sqrt 3 / 8 * cos α ^ 2 * sin α - 9 / 8 * cos α * sin α ^ 2 - 3 * Real.sqrt 3 / 8 * sin α^3) + (-1/8 * cos α ^ 3 + 3 * Real.sqrt 3 / 8 * cos α ^ 2 * sin α - 9 / 8 * cos α * sin α ^ 2 + 3 * Real.sqrt 3 / 8 * sin α^3) := by
            rw [h100, h110]
      _ = 3 / 4 * cos α ^ 3 - 9 / 4 * cos α * sin α ^ 2 := by 
        ring_nf
      _ = 3 / 4 * (4 * cos α ^ 3 - 3 * cos α) := by 
        have h14 : sin α ^ 2 = 1 - cos α ^ 2 := by
          have h99 : cos α ^ 2 + sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
          linarith
        rw [h14]
        ring_nf
  linarith [h10]