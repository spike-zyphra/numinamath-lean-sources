import Mathlib

theorem number_theory_217299 : 37 ∣ (8888^2222 + 7777^3333) := by
  norm_num [Nat.dvd_iff_mod_eq_zero]