import Mathlib

open Real

theorem algebra_212155 : tan (15 * π / 180) + cot (15 * π / 180) = 4 := by
  have h1 : tan (15 * π / 180) = sin (15 * π / 180) / cos (15 * π / 180) := by 
    rw [tan_eq_sin_div_cos]
  have h2 : cot (15 * π / 180) = cos (15 * π / 180) / sin (15 * π / 180) := by 
    rw [cot_eq_cos_div_sin]
  rw [h1, h2]
  have h3 : sin (15 * π / 180) ≠ 0 := by
    have h3 : 0 < 15 * π / 180 := by 
      have h4 : 0 < π := Real.pi_pos
      nlinarith [Real.pi_gt_31415]
    have h4 : sin (15 * π / 180) > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith [Real.pi_gt_31415]
    linarith
  have h4 : cos (15 * π / 180) ≠ 0 := by
    have h5 : 0 < 15 * π / 180 := by 
      have h4 : 0 < π := Real.pi_pos
      nlinarith [Real.pi_gt_31415]
    have h6 : cos (15 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      all_goals linarith [Real.pi_gt_31415]
    linarith
  have h5 : sin (15 * π / 180) ^ 2 + cos (15 * π / 180) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (15 * π / 180)
  have h7 : 2 * (15 * π / 180) = Real.pi / 6 := by 
    ring_nf
  have h8 : sin (2 * (15 * π / 180)) = 1 / 2 := by 
    rw [h7]
    rw [sin_pi_div_six]
  have h9 : sin (15 * π / 180) * cos (15 * π / 180) = 1 / 4 := by 
    have h6 : sin (15 * π / 180) * cos (15 * π / 180) = (1 / 2) * sin (2 * (15 * π / 180)) := by 
      rw [sin_two_mul]
      <;> ring
    rw [h6, h8]
    norm_num
  have eq3 : sin (15 * π / 180) / cos (15 * π / 180) + cos (15 * π / 180) / sin (15 * π / 180) = (sin (15 * π / 180) ^ 2 + cos (15 * π / 180) ^ 2) / (sin (15 * π / 180) * cos (15 * π / 180)) := by
    have h10 : sin (15 * π / 180) ≠ 0 := h3
    have h11 : cos (15 * π / 180) ≠ 0 := h4
    have eq3a : sin (15 * π / 180) / cos (15 * π / 180) + cos (15 * π / 180) / sin (15 * π / 180) = (sin (15 * π / 180) * sin (15 * π / 180) + cos (15 * π / 180) * cos (15 * π / 180)) / (cos (15 * π / 180) * sin (15 * π / 180)) := by
      field_simp [h10, h11]
      <;> ring
    have eq3b : (sin (15 * π / 180) * sin (15 * π / 180) + cos (15 * π / 180) * cos (15 * π / 180)) / (cos (15 * π / 180) * sin (15 * π / 180)) = (sin (15 * π / 180) ^ 2 + cos (15 * π / 180) ^ 2) / (sin (15 * π / 180) * cos (15 * π / 180)) := by
      have h15 : sin (15 * π / 180) * cos (15 * π / 180) = cos (15 * π / 180) * sin (15 * π / 180) := by 
        ring
      have h16 : sin (15 * π / 180) ^ 2 + cos (15 * π / 180) ^ 2 = sin (15 * π / 180) * sin (15 * π / 180) + cos (15 * π / 180) * cos (15 * π / 180) := by 
        ring
      rw [h16, h15]
    rw [eq3a, eq3b]
  rw [eq3]
  rw [h5, h9]
  all_goals norm_num