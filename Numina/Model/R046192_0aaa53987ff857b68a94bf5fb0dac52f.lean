import Mathlib

theorem number_theory_13416 : multiplicity 10 (Nat.factorial 2021) = 503 := by
  have h1 : multiplicity 10 (Nat.factorial 2021) = 503 := by
    rw [multiplicity_eq_of_dvd_of_not_dvd]
    all_goals native_decide
  exact h1