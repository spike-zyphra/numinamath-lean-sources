import Mathlib

theorem number_theory_16476 : multiplicity 10 (Nat.factorial 1000) = 249 := by
  rw [multiplicity_eq_of_dvd_of_not_dvd]
  all_goals 
    native_decide