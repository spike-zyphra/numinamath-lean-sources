import Mathlib

theorem number_theory_135462 : 641 ∣ 2^32 + 1 ∧ 421 ∣ 1280000401 := by 
  constructor
  · -- Show that 641 divides 2^32 + 1
    norm_num
  · -- Show that 421 divides 1280000401
    norm_num