import Mathlib

theorem number_theory_282168 : ¬ ( 31 ∣ (6^1962 + 1)) := by 
  norm_num [Nat.dvd_iff_mod_eq_zero]