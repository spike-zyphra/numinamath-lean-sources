import Mathlib

open Real

theorem algebra_250917 : (sin (53 * π / 180) - 2 * cos (40 * π / 180) * sin (13 * π / 180)) / cos (63 * π / 180) = 1 := by

  have h1 : sin (53 * π / 180) - 2 * cos (40 * π / 180) * sin (13 * π / 180) = sin (27 * π / 180) := by
    have h2 : 2 * cos (40 * π / 180) * sin (13 * π / 180) = sin (53 * π / 180) - sin (27 * π / 180) := by
      have h3 : sin (53 * π / 180) = sin (40 * π / 180 + 13 * π / 180) := by
        ring_nf
      have h4 : sin (27 * π / 180) = sin (40 * π / 180 - 13 * π / 180) := by
        ring_nf
      rw [h3, h4]
      rw [sin_add, sin_sub]
      all_goals ring_nf <;> simp [Real.sin_sq, Real.cos_sq] <;> ring_nf <;> norm_num
      <;> nlinarith

    linarith [h2]

  have h2 : sin (27 * π / 180) = cos (63 * π / 180) := by
    have h3 : 27 * π / 180 = (Real.pi / 2) - (63 * π / 180) := by
      nlinarith [Real.pi_pos]
    rw [h3]
    rw [sin_pi_div_two_sub]

  have h3 : cos (63 * π / 180) ≠ 0 := by
    have h1 : 0 < (63 * π / 180 : ℝ) := by
      nlinarith [Real.pi_pos]
    have h2 : (63 * π / 180 : ℝ) < Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have h3 : cos (63 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> linarith [Real.pi_pos]
    nlinarith

  rw [h1, h2]
  field_simp [h3]
  <;> nlinarith [Real.pi_pos]