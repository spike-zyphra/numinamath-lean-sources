import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_106676 : arctan (2/3) + arctan (1/5) = π/4 := by
  have h : arctan (2 / 3) + arctan (1 / 5) = arctan ((2 / 3 + 1 / 5) / (1 - (2 / 3) * (1 / 5))) := by
    rw [Real.arctan_add]
    all_goals norm_num
  have h2 : (2 / 3 + 1 / 5 : ℝ) / (1 - (2 / 3) * (1 / 5) : ℝ) = (1 : ℝ) := by
    norm_num
  rw [h]
  rw [h2] at *
  all_goals norm_num [Real.arctan_one]
  all_goals linarith [Real.pi_pos]