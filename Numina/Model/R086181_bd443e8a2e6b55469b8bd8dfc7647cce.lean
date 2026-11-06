import Mathlib

open Real

theorem algebra_5154 : tan (10 * π / 180) * (cot (10 * π / 180) - 2 * cos (70 * π / 180)) = 2 * sin (70 * π / 180) - 1 := by
  have htan : tan (10 * π / 180) = sin (10 * π / 180) / cos (10 * π / 180) := by 
    rw [tan_eq_sin_div_cos]
  have hcot : cot (10 * π / 180) = cos (10 * π / 180) / sin (10 * π / 180) := by
    rw [cot_eq_cos_div_sin]
  rw [htan, hcot]
  have h1 : sin (10 * π / 180) ≠ 0 := by
    have h2 : 0 < 10 * π / 180 := by 
      have h3 : 0 < π := Real.pi_pos
      nlinarith [Real.pi_gt_three]
    have h4 : sin (10 * π / 180) > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      linarith [h2]
      linarith [h2, Real.pi_gt_three]
    linarith
  have h2 : cos (10 * π / 180) ≠ 0 := by
    have h3 : -π/2 < 10 * π / 180 := by 
      nlinarith [Real.pi_gt_three]
    have h4 : cos (10 * π / 180) > 0 := by 
      apply cos_pos_of_mem_Ioo
      constructor
      nlinarith [Real.pi_gt_three]
      linarith [Real.pi_gt_three]
    linarith
  field_simp [h1, h2]
  have h3 : cos (70 * π / 180) = sin (20 * π / 180) := by
    have h1 : 70 * π / 180 = π / 2 - 20 * π / 180 := by
      nlinarith [Real.pi_gt_three]
    rw [h1]
    rw [cos_pi_div_two_sub]
  rw [h3]
  have h4 : sin (70 * π / 180) = cos (20 * π / 180) := by
    have h1 : 70 * π / 180 = π / 2 - 20 * π / 180 := by
      nlinarith [Real.pi_gt_three]
    rw [h1]
    rw [sin_pi_div_two_sub]
  rw [h4]
  have h5 : sin (20 * π / 180) = 2 * sin (10 * π / 180) * cos (10 * π / 180) := by
    rw [show 20 * π / 180 = 2 * (10 * π / 180) by ring_nf <;> linarith [Real.pi_gt_three]]
    rw [sin_two_mul]
  rw [h5]
  have h6 : cos (20 * π / 180) = 1 - 2 * sin (10 * π / 180)^2 := by
    have h7 : 20 * π / 180 = 2 * (10 * π / 180) := by
      ring_nf
      <;> linarith [Real.pi_gt_three]
    rw [h7]
    rw [cos_two_mul]
    <;> try simp [sin_sq]
    <;> try nlinarith [sin_sq_add_cos_sq (10 * π / 180)]
  rw [h6]
  nlinarith [sin_sq_add_cos_sq (10 * π / 180), Real.pi_pos]