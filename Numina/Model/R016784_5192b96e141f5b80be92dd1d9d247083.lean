import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_315104 : 2 * arctan (1 / 5) + arctan (1 / 4) = arctan (32 / 43) := by
  have h1 : 2 * arctan (1 / 5) = arctan (5 / 12) := by
    have h2 : 2 * arctan (1 / 5) = arctan (2 * (1 / 5) / (1 - (1 / 5) ^ 2)) := by 
      rw [show 2 * arctan (1 / 5) = arctan (1 / 5) + arctan (1 / 5) by ring]
      rw [arctan_add]
      all_goals norm_num
    rw [h2]
    all_goals norm_num 
  have h3 : arctan (5 / 12) + arctan (1 / 4) = arctan (32 / 43) := by 
    rw [arctan_add]
    all_goals norm_num 
  calc
    2 * arctan (1 / 5) + arctan (1 / 4)
        = (2 * arctan (1 / 5)) + arctan (1 / 4) := by ring
    _ = arctan (5 / 12) + arctan (1 / 4) := by rw [h1]
    _ = arctan (32 / 43) := by rw [h3]