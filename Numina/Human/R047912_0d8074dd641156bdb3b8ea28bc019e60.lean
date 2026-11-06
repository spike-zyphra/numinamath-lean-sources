import Mathlib

theorem number_theory_177699 : 7 ∣ (2222^5555 + 5555^2222) := by 
  norm_num [Nat.dvd_iff_mod_eq_zero]