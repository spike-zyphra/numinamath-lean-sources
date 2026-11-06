import Mathlib

open Real
theorem algebra_215368 : 
  1 / tan (70 * π / 180) + 4 * cos (70 * π / 180) = sqrt 3 := by 
  have h1 : 1 / tan (70 * π / 180) = cos (70 * π / 180) / sin (70 * π / 180) := by
    rw [tan_eq_sin_div_cos]
    field_simp
  rw [h1]
  have h2 : sin (70 * π / 180) ≠ 0 := by
    have h3 : 0 < 70 * π / 180 := by
      nlinarith [Real.pi_pos, Real.pi_gt_three]
    have h4 : sin (70 * π / 180) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals 
        nlinarith [Real.pi_pos, Real.pi_gt_three]
    nlinarith
  have eq1 : cos (70 * π / 180) / sin (70 * π / 180) + 4 * cos (70 * π / 180) = 
    (cos (70 * π / 180) + 4 * cos (70 * π / 180) * sin (70 * π / 180)) / sin (70 * π / 180) := by
    field_simp [h2]
    <;> ring_nf <;> field_simp
    <;> tauto
  rw [eq1]
  have eq2 : cos (70 * π / 180) + 4 * cos (70 * π / 180) * sin (70 * π / 180) = 
          Real.sqrt 3 * sin (70 * π / 180) := by
    have h3 : sin (70 * π / 180) = cos (20 * π / 180) := by
      have h4 : 70 * π / 180 = Real.pi / 2 - 20 * π / 180 := by
        nlinarith [Real.pi_pos, Real.pi_gt_three]
      rw [h4]
      rw [sin_pi_div_two_sub]
      all_goals nlinarith [Real.pi_pos, Real.pi_gt_three]
    have h4 : cos (70 * π / 180) = sin (20 * π / 180) := by
      have h5 : 70 * π / 180 = Real.pi / 2 - 20 * π / 180 := by
        nlinarith [Real.pi_pos, Real.pi_gt_three]
      rw [h5]
      rw [cos_pi_div_two_sub]
      all_goals nlinarith [Real.pi_pos, Real.pi_gt_three]
    rw [h3, h4]
    have eq3 : sin (20 * π / 180) + 4 * sin (20 * π / 180) * cos (20 * π / 180) = 
          Real.sqrt 3 * cos (20 * π / 180) := by
      have h5 : sin (20 * π / 180) + 4 * sin (20 * π / 180) * cos (20 * π / 180) = 
          sin (20 * π / 180) + 2 * (2 * sin (20 * π / 180) * cos (20 * π / 180)) := by ring
      rw [h5]
      have h6 : 2 * sin (20 * π / 180) * cos (20 * π / 180) = sin (40 * π / 180) := by
        have h7 : sin (40 * π / 180) = 2 * sin (20 * π / 180) * cos (20 * π / 180) := by
          rw [show 40 * π / 180 = 2 * (20 * π / 180) by ring]
          rw [sin_two_mul]
          all_goals ring
        linarith [h7]
      have h7 : sin (40 * π / 180) = sin (π / 3) * cos (20 * π / 180) - cos (π / 3) * sin (20 * π / 180) := by
        have h8 : 40 * π / 180 = (π / 3) - (20 * π / 180) := by
          nlinarith [Real.pi_pos]
        rw [h8]
        rw [sin_sub]
        <;> ring_nf <;> field_simp [Real.sin_pi_div_three, Real.cos_pi_div_three] <;> nlinarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < 20 * π / 180 by nlinarith [Real.pi_pos] ) (show 20 * π / 180 < Real.pi by nlinarith [Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < π / 3 by nlinarith [Real.pi_pos] ) (show π / 3 < Real.pi by nlinarith [Real.pi_pos]), Real.sin_pi_div_three, Real.cos_pi_div_three]
      have h8 : sin (20 * π / 180) + 2 * sin (40 * π / 180) = Real.sqrt 3 * cos (20 * π / 180) := by
        rw [h7]
        have h9 : sin (π / 3) = Real.sqrt 3 / 2 := by
          exact sin_pi_div_three
        have h10 : cos (π / 3) = 1 / 2 := by
          exact cos_pi_div_three
        rw [h9, h10]
        all_goals linarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < 20 * π / 180 by nlinarith [Real.pi_pos] ) (show 20 * π / 180 < Real.pi by nlinarith [Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < π / 3 by nlinarith [Real.pi_pos] ) (show π / 3 < Real.pi by nlinarith [Real.pi_pos]), Real.sin_pi_div_three, Real.cos_pi_div_three]
      have h9 : sin (20 * π / 180) + 2 * (2 * sin (20 * π / 180) * cos (20 * π / 180)) = sin (20 * π / 180) + 2 * sin (40 * π / 180) := by
        rw [h6]
        all_goals ring
      linarith [h8, h9]
    linarith [eq3]
  have eq3 : (cos (70 * π / 180) + 4 * cos (70 * π / 180) * sin (70 * π / 180)) / sin (70 * π / 180) = sqrt 3 := by
    rw [eq2]
    field_simp [h2]
    all_goals linarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num)]
  linarith [eq3]