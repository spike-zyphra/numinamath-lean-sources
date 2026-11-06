import Mathlib

open Real

theorem algebra_13674 : arctan 1 + arctan (1 / 2) + arctan (1 / 3) = π / 2 := by
  have h1 : arctan 1 = π / 4 := by
    simp [arctan_one]
  
  have h2 : arctan (1 / 2) + arctan (1 / 3) = π / 4 := by
    have h : arctan (1 / 2) + arctan (1 / 3) = arctan ((1 / 2 + 1 / 3) / (1 - (1 / 2) * (1 / 3))) := by
      rw [arctan_add]
      all_goals norm_num
    rw [h]
    norm_num [arctan_one]

  linarith [h1, h2]