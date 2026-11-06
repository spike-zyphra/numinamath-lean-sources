import Mathlib

theorem number_theory_197368 :
    83 ∣ 2^41 + 1 ∧ 13 ∣ 2^70 + 3^70 ∧ 20801 ∣ 2^60 - 1 := by
  constructor
  · -- Show that 83 divides 2^41 + 1
    norm_num
  constructor
  · -- Show that 13 divides 2^70 + 3^70
    norm_num
  · -- Show that 20801 divides 2^60 - 1
    norm_num