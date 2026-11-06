import Mathlib

open Real Set
open scoped Real

theorem algebra_96451 : cot (10 * π / 180) + tan (5 * π / 180) = 1 / sin (10 * π / 180) := by
  have htan : tan (5 * π / 180) = sin (5 * π / 180) / cos (5 * π / 180) := by
    rw [tan_eq_sin_div_cos]
  have hcot : cot (10 * π / 180) = cos (10 * π / 180) / sin (10 * π / 180) := by
    rw [cot_eq_cos_div_sin]
  rw [hcot, htan]

  have h5 : cos (5 * π / 180) ≠ 0 := by
    have h1 : 0 < 5 * π / 180 := by 
      nlinarith [Real.pi_pos, Real.pi_gt_three]
    have h2 : 5 * π / 180 < Real.pi / 2 := by 
      nlinarith [Real.pi_gt_three, Real.pi_lt_31416]
    have h3 : cos (5 * π / 180) > 0 := by 
      apply cos_pos_of_mem_Ioo
      constructor 
      · linarith 
      · linarith 
    linarith [h3]

  have h6 : sin (10 * π / 180) ≠ 0 := by 
    have h1 : 0 < 10 * π / 180 := by 
      nlinarith [Real.pi_pos, Real.pi_gt_three]
    have h2 : 10 * π / 180 < Real.pi := by 
      nlinarith [Real.pi_gt_three, Real.pi_lt_31416]
    have h3 : sin (10 * π / 180) > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith
    linarith [h3]

  have h7 : cos (10 * π / 180) / sin (10 * π / 180) + sin (5 * π / 180) / cos (5 * π / 180) = 1 / sin (10 * π / 180) := by
    have h8 : cos (10 * π / 180) / sin (10 * π / 180) + sin (5 * π / 180) / cos (5 * π / 180) = (cos (10 * π / 180) * cos (5 * π / 180) + sin (10 * π / 180) * sin (5 * π / 180)) / (sin (10 * π / 180) * cos (5 * π / 180)) := by
      field_simp [h6, h5]
      <;> ring
    have h9 : cos (10 * π / 180) * cos (5 * π / 180) + sin (10 * π / 180) * sin (5 * π / 180) = cos (5 * π / 180) := by 
      have h10 : cos (10 * π / 180) * cos (5 * π / 180) + sin (10 * π / 180) * sin (5 * π / 180) = cos (10 * π / 180 - 5 * π / 180) := by 
        rw [cos_sub]
        <;> ring_nf
      rw [h10]
      ring_nf
    rw [h8]
    rw [h9]
    have h10 : cos (5 * π / 180) ≠ 0 := h5
    have h11 : sin (10 * π / 180) ≠ 0 := h6
    field_simp [h11, h10]
    <;> ring
  linarith [h7]