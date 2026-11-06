import Mathlib

theorem number_theory_99871 : multiplicity 10 (∏ i ∈ Finset.Icc 1 2020, if i % 5 = 0 then i else 1) = 400 := by 
  rw [multiplicity_eq_of_dvd_of_not_dvd]
  all_goals native_decide