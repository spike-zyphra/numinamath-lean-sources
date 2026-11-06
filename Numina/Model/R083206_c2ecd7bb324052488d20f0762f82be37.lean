import Mathlib

theorem number_theory_223984 (n : ℕ) (h₀ : n > 0) (h₁ : 1010 % n = 0)
    (h₂ : (1010 / n) * 2 = 1010 - (1010 / n)) :
    n = 30 := by

  have h4 : n ≤ 1010 := by
    have h5 : n ∣ 1010 := by
      exact Nat.dvd_of_mod_eq_zero h₁
    exact Nat.le_of_dvd (by norm_num) h5

  interval_cases n <;> norm_num at h₁ h₂ <;> all_goals omega