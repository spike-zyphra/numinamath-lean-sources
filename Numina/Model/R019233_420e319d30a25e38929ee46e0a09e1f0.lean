import Mathlib

theorem number_theory_230275 {d r : ℕ} (h₀ : d ≠ 0) (h₁ : 2017 % d = r) (h₂ : 1029 % d = r)
    (h₃ : 725 % d = r) :
    d - r ≤ 35 := by
  have h4 : d ∣ 988 := by
    have h7 : (2017 : ℕ) % d = (1029 : ℕ) % d := by 
      omega
    have h8 : d ∣ (2017 : ℕ) - (1029 : ℕ) := by
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h7)
    have h9 : (2017 : ℕ) - (1029 : ℕ) = 988 := by
      omega
    rw [h9] at h8
    exact h8
  have h5 : d ∣ 304 := by
    have h7 : (1029 : ℕ) % d = (725 : ℕ) % d := by 
      omega
    have h8 : d ∣ (1029 : ℕ) - (725 : ℕ) := by 
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h7)
    have h9 : (1029 : ℕ) - (725 : ℕ) = 304 := by
      omega
    rw [h9] at h8
    exact h8
  have h6 : d ∣ 76 := by
    exact Nat.dvd_gcd h4 h5
  have h7 : d ≤ 76 := by
    exact Nat.le_of_dvd (by linarith) h6
  have h8 : r < d := by
    have h9 : 725 % d = r := h₃
    have h10 : 725 % d < d := by
      apply Nat.mod_lt 
      all_goals 
        omega
    linarith [h9, h10]
  interval_cases d <;> omega