import Mathlib

open Finset

theorem number_theory_610871 : multiplicity 24 (Nat.factorial 100) = 32 := by
  rw [multiplicity_eq_of_dvd_of_not_dvd]
  all_goals native_decide