import Mathlib

open Real

theorem algebra_199041 : 15 * tan (44 * π / 180) * tan (45 * π / 180) * tan (46 * π / 180) = 15 := by 
  have htan1 : tan (45 * π / 180) = 1 := by 
    have h1 : 45 * π / 180 = π / 4 := by 
      ring_nf
    rw [h1]
    rw [tan_pi_div_four]
  have htan2 : tan (44 * π / 180) * tan (46 * π / 180) = 1 := by
    have h1 : 46 * π / 180 = π / 2 - (44 * π / 180) := by
      ring_nf
    have htan3 : tan (π / 2 - (44 * π / 180)) = cos (44 * π / 180) / sin (44 * π / 180) := by 
      rw [tan_eq_sin_div_cos]
      have htan4 : sin (π / 2 - (44 * π / 180)) = cos (44 * π / 180) := by 
        rw [sin_pi_div_two_sub]
      have htan5 : cos (π / 2 - (44 * π / 180)) = sin (44 * π / 180) := by
        rw [cos_pi_div_two_sub]
      simp [htan4, htan5]
      <;> ring_nf 
      <;> simp [sin_sq_add_cos_sq] 
      all_goals try tauto 
      all_goals try nlinarith 
      all_goals ring_nf 
      all_goals nlinarith 
    rw [h1]
    rw [htan3]
    -- Product is 1
    have htan4 : sin (44 * π / 180) ≠ 0 := by 
      have h1 : 0 < 44 * π / 180 := by
        nlinarith [Real.pi_pos]
      have h2 : 44 * π / 180 < Real.pi := by
        nlinarith [Real.pi_pos, Real.pi_gt_three]
      have h3 : sin (44 * π / 180) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        linarith [Real.pi_pos]
        linarith [Real.pi_pos, Real.pi_gt_three]
      linarith
    have htan5 : cos (44 * π / 180) ≠ 0 := by 
      have h1 : 0 < 44 * π / 180 := by
        nlinarith [Real.pi_pos]
      have h2 : 44 * π / 180 < Real.pi / 2 := by
        nlinarith [Real.pi_pos, Real.pi_gt_three]
      have h3 : cos (44 * π / 180) > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor <;> linarith
      linarith
    have htan6 : tan (44 * π / 180) = sin (44 * π / 180) / cos (44 * π / 180) := by 
      rw [tan_eq_sin_div_cos]
    rw [htan6]
    field_simp [htan4, htan5]
    <;> ring_nf <;> field_simp
    all_goals try linarith
    all_goals try tauto
    all_goals try nlinarith 
    all_goals try tauto 
    all_goals ring_nf 
    all_goals nlinarith 
  calc
    15 * tan (44 * π / 180) * tan (45 * π / 180) * tan (46 * π / 180)
        = 15 * (tan (44 * π / 180) * tan (45 * π / 180) * tan (46 * π / 180)) := by ring
    _ = 15 * (tan (44 * π / 180) * tan (46 * π / 180) * tan (45 * π / 180)) := by ring
    _ = 15 * (tan (44 * π / 180) * tan (46 * π / 180) * 1) := by rw [htan1]
    _ = 15 * (1 * 1) := by rw [htan2]
    _ = 15 := by ring