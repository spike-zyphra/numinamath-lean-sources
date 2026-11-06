import Mathlib

open Real Set
open scoped Real

theorem inequalities_197720 : tan (40 * π / 180) + tan (45 * π / 180) + tan (50 * π / 180) > 3 := by
  have htan1 : tan (45 * π / 180) = 1 := by 
    have h1 : 45 * π / 180 = π / 4 := by
      ring_nf
    rw [h1]
    rw [tan_pi_div_four]
  
  have htan2 : tan (50 * π / 180) = 1 / (tan (40 * π / 180)) := by
    have h1 : 50 * π / 180 = π / 2 - 40 * π / 180 := by
      ring_nf
    rw [h1]
    have ht1 : tan (π / 2 - 40 * π / 180) = (cos (40 * π / 180) / sin (40 * π / 180)) := by 
      rw [tan_eq_sin_div_cos]
      have ht2 : sin (π / 2 - 40 * π / 180) = cos (40 * π / 180) := by
        rw [sin_pi_div_two_sub]
      have ht3 : cos (π / 2 - 40 * π / 180) = sin (40 * π / 180) := by
        rw [cos_pi_div_two_sub]
      rw [ht2, ht3]
    
    rw [ht1]
    
    have ht2 : tan (40 * π / 180) = (sin (40 * π / 180) / cos (40 * π / 180)) := by 
      rw [tan_eq_sin_div_cos]
    
    rw [ht2]
    
    field_simp [show cos (40 * π / 180) ≠ 0 by
      have : cos (40 * π / 180) > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor <;> nlinarith [pi_pos, Real.pi_gt_three]
      linarith
    , show sin (40 * π / 180) ≠ 0 by
      have : sin (40 * π / 180) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        all_goals nlinarith [pi_pos, Real.pi_gt_three]
      linarith
    ]
  
  have h6 : tan (40 * π / 180) + tan (50 * π / 180) > 2 := by
    rw [htan2]
    
    have htan4 : 0 < tan (40 * π / 180) := by
      apply tan_pos_of_pos_of_lt_pi_div_two
      all_goals nlinarith [pi_pos, Real.pi_gt_three]
    
    have htan3 : tan (40 * π / 180) < 1 := by
      have ht1 : tan (40 * π / 180) < tan (45 * π / 180) := by
        apply Real.tan_lt_tan_of_lt_of_lt_pi_div_two
        all_goals nlinarith [pi_pos, Real.pi_gt_three]
      have ht2 : tan (45 * π / 180) = 1 := htan1
      linarith [ht1, ht2]
    
    have ht5 : (tan (40 * π / 180) + 1 / tan (40 * π / 180)) - 2 > 0 := by
      have ht6 : (tan (40 * π / 180) + 1 / tan (40 * π / 180)) - 2 = ( (tan (40 * π / 180) - 1)^2 ) / tan (40 * π / 180) := by
        field_simp [show 0 < tan (40 * π / 180) by linarith [htan4]]
        ring
      rw [ht6]
      apply div_pos
      · -- (tan (40 * π / 180) - 1) ^ 2 > 0
        have ht7 : tan (40 * π / 180) ≠ 1 := by
          linarith [htan3]
        have ht8 : (tan (40 * π / 180) - 1) ^ 2 > 0 := by
          apply pow_two_pos_of_ne_zero
          intro h
          apply ht7
          linarith
        linarith
      · -- tan (40 * π / 180) > 0
        linarith [htan4]
    
    linarith [ht5]
    
  linarith [htan1, h6]