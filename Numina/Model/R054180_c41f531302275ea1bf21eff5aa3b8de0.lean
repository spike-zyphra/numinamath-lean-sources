import Mathlib

theorem number_theory_112199 : ¬ 4 ∣ 17^15 - 3^15 := by
  norm_num [Nat.dvd_iff_mod_eq_zero]