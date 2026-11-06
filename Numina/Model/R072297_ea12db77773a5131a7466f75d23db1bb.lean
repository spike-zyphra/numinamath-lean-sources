import Mathlib

open Real Set
open scoped Real

theorem algebra_145902 : ((1 - sin (30 * π / 180)) * (1 + cos (60 * π / 180))) / ((1 + cos (30 * π / 180)) * (1 - sin (60 * π / 180))) / (2 + tan (45 * π / 180))^2 = 1 / 3 := by
  have h1 : sin (30 * π / 180) = 1 / 2 := by
    have h1 : 30 * π / 180 = π / 6 := by
      linarith [Real.pi_pos]
    rw [h1]
    exact Real.sin_pi_div_six
  have h2 : cos (60 * π / 180) = 1 / 2 := by
    have h2 : 60 * π / 180 = π / 3 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [Real.cos_pi_div_three]
  have h3 : cos (30 * π / 180) = Real.sqrt 3 / 2 := by
    have h3 : 30 * π / 180 = π / 6 := by
      linarith [Real.pi_pos]
    rw [h3]
    rw [Real.cos_pi_div_six]
  have h4 : sin (60 * π / 180) = Real.sqrt 3 / 2 := by
    have h4 : 60 * π / 180 = π / 3 := by
      linarith [Real.pi_pos]
    rw [h4]
    rw [Real.sin_pi_div_three]
  have h5 : tan (45 * π / 180) = 1 := by
    have h5 : 45 * π / 180 = π / 4 := by
      linarith [Real.pi_pos]
    rw [h5]
    rw [Real.tan_pi_div_four]
  rw [h1, h2, h3, h4, h5]
  field_simp
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num