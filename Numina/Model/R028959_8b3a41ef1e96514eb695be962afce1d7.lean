import Mathlib

theorem number_theory_179850 : 61 ∣ (2^888 - 888) := by
  norm_num [Nat.dvd_iff_mod_eq_zero]