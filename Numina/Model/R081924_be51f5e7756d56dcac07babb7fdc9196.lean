import Mathlib

theorem algebra_21678 : (5 / Real.sqrt 3 : ℝ) = 5 * Real.sqrt 3 / 3 := by 
  have h1 : Real.sqrt 3 > 0 := by
    positivity
  field_simp
  <;> ring_nf <;> norm_num <;> ring
  <;> norm_num