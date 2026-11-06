import Mathlib

open Real

theorem calculus_22295 : tan (210 * π / 180) = √3 / 3 := by
  have h : 210 * π / 180 = π + π / 6 := by 
    linarith [pi_pos]
  rw [h]
  have htan1 : tan (π + π / 6) = tan (π / 6) := by
    rw [show π + π / 6 = π / 6 + Real.pi by ring]
    rw [tan_add_pi]
  rw [htan1]
  have htan2 : tan (π / 6) = 1 / Real.sqrt 3 := by
    have htan2 : tan (π / 6) = (sin (π / 6)) / (cos (π / 6)) := by
      rw [tan_eq_sin_div_cos]
    rw [htan2]
    have htan3 : sin (π / 6) = 1 / 2 := sin_pi_div_six
    have htan4 : cos (π / 6) = Real.sqrt 3 / 2 := by 
      have htan5 : cos (π / 6) = Real.sqrt 3 / 2 := cos_pi_div_six
      exact htan5
    rw [htan3, htan4]
    <;> field_simp <;> ring_nf <;> field_simp
  rw [htan2]
  have : (1 / Real.sqrt 3 : ℝ) = Real.sqrt 3 / 3 := by
    field_simp
    <;> ring_nf
    <;> field_simp
  linarith [this]