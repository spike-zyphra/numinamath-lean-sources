import Mathlib

open Real

theorem algebra_225493 : arctan (1 / 3) + arctan (1 / 5) + arctan (1 / 7) + arctan (1 / 8) = π / 4 := by 
  have h1 : arctan (1 / 3) + arctan (1 / 5) = arctan (4 / 7) := by 
    rw [arctan_add]
    norm_num
    all_goals norm_num
  have h2 : arctan (4 / 7) + arctan (1 / 7) = arctan (7 / 9) := by 
    rw [arctan_add]
    norm_num
    all_goals norm_num
  have h3 : arctan (7 / 9) + arctan (1 / 8) = arctan 1 := by 
    rw [arctan_add]
    norm_num
    all_goals norm_num
  rw [h1, h2, h3]
  rw [arctan_one]
  all_goals linarith [Real.pi_pos]