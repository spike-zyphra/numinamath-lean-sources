import Mathlib

theorem number_theory_293561 (r d : ℕ) (h₀ : 2017 % d = r) (h₁ : 1029 % d = r) (h₂ : 725 % d = r) :
    d - r ≤ 35 := by
  by_cases h3 : d > 2017
  · -- Assume that d > 2017
    have h4 : 2017 % d = 2017 := by
      rw [Nat.mod_eq_of_lt]
      all_goals linarith
    have h5 : 1029 % d = 1029 := by
      rw [Nat.mod_eq_of_lt]
      all_goals linarith
    have h6 : 725 % d = 725 := by
      rw [Nat.mod_eq_of_lt]
      all_goals linarith
    omega
  · -- Assume that d ≤ 2017
    have h3 : d ≤ 2017 := by
      omega
    interval_cases d <;> omega