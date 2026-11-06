import Mathlib

open Real

theorem algebra_107373 : 4 * arctan (1 / 5) - arctan (1 / 239) = π / 4 := by
  have h1 : 4 * arctan (1 / 5) = arctan (120 / 119) := by
    have h2 : 2 * arctan (1 / 5) = arctan (5 / 12) := by
      rw [show 2 * arctan (1 / 5) = arctan (1 / 5) + arctan (1 / 5) by ring]
      rw [arctan_add]
      all_goals norm_num
    have h3 : 4 * arctan (1 / 5) = 2 * (2 * arctan (1 / 5)) := by ring
    rw [h3, h2]
    have h4 : 2 * arctan (5 / 12) = arctan (120 / 119) := by
      rw [show 2 * arctan (5 / 12) = arctan (5 / 12) + arctan (5 / 12) by ring]
      rw [arctan_add]
      all_goals norm_num
    linarith
  have h7 : arctan (120 / 119) - arctan (1 / 239) = π / 4 := by 
    have h8 : arctan (120 / 119) - arctan (1 / 239) = arctan (1) := by 
      have h9 : arctan (120 / 119) - arctan (1 / 239) = arctan (120 / 119) + arctan (- (1 / 239)) := by 
        have h10 : arctan (120 / 119) - arctan (1 / 239) = arctan (120 / 119) + -arctan (1 / 239) := by ring
        rw [h10]
        have h11 : - arctan (1 / 239) = arctan (- (1 / 239)) := by 
          rw [show -arctan (1 / 239) = arctan (- (1 / 239)) by 
            rw [arctan_neg]
          ]
        rw [h11]
      rw [h9]
      rw [arctan_add]
      all_goals norm_num [arctan_one]
    rw [h8]
    all_goals linarith [Real.arctan_one]
  
  have h8' : 4 * arctan (1 / 5) - arctan (1 / 239) = arctan (120 / 119) - arctan (1 / 239) := by
    linarith [h1]
  rw [h8']
  linarith [h7]