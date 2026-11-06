import Mathlib
set_option maxRecDepth 10000000000

theorem number_theory_1849 : multiplicity 10 (Nat.factorial 2005) = 500 := by 
  rw [multiplicity_eq_of_dvd_of_not_dvd]
  all_goals
    native_decide