import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_22219 : arctan (-1 / sqrt 3) = -π / 6 := by
  have h1 : sin (π / 6) = 1 / 2 := Real.sin_pi_div_six
  have h2 : cos (π / 6) = sqrt 3 / 2 := Real.cos_pi_div_six
  have h3 : tan (π / 6) = 1 / sqrt 3 := by
    rw [tan_eq_sin_div_cos, h1, h2]
    field_simp
  
  have h4 : tan (-π / 6) = -1 / sqrt 3 := by
    have h5 : tan (-π / 6) = -tan (π / 6) := by
      rw [← Real.tan_neg]
      -- Angle simplification
      ring_nf
    rw [h5]
    rw [h3]
    <;> ring_nf <;> field_simp

  rw [← h4]
  rw [Real.arctan_tan]
  all_goals
    ring_nf <;> linarith [Real.pi_pos]