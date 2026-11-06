import Mathlib

theorem number_theory_210358 (d : ℕ) (hd : d > 1) (h : 1059 % d = 1417 % d ∧ 1417 % d = 2312 % d) :
    d = 179 := by
  have h1 : 1059 % d = 1417 % d := by
    omega
  have h2 : 1417 % d = 2312 % d := by
    omega
  have h3 : d ∣ 358 := by
    have h4 : (1417 : ℕ) % d = (1059 : ℕ) % d := by 
      omega
    have : d ∣ (1417 : ℕ) - (1059 : ℕ) := by 
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq 
        h4
      )
    have : d ∣ (1417 - 1059 : ℕ) := by 
      exact this
    have h5 : (1417 : ℕ) - (1059 : ℕ) = 358 := by omega
    rw [h5] at this
    exact this
  have h4 : d ∣ 895 := by 
    have h5 : (2312 : ℕ) % d = (1417 : ℕ) % d := by 
      omega
    have : d ∣ (2312 : ℕ) - (1417 : ℕ) := by 
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq 
        h5
      )
    have : d ∣ (2312 - 1417 : ℕ) := by 
      exact this
    have h6 : (2312 : ℕ) - (1417 : ℕ) = 895 := by omega
    rw [h6] at this
    exact this
  have h5 : d ∣ 1253 := by
    have h6 : (2312 : ℕ) % d = (1059 : ℕ) % d := by 
      omega
    have : d ∣ (2312 : ℕ) - (1059 : ℕ) := by 
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq 
        h6
      )
    have : d ∣ (2312 - 1059 : ℕ) := by 
      exact this
    have h7 : (2312 : ℕ) - (1059 : ℕ) = 1253 := by omega
    rw [h7] at this
    exact this
  have h6 : d ∣ 179 := by 
    exact Nat.dvd_gcd (Nat.dvd_gcd h3 h4) h5
  have h7 : d = 179 := by
    have h8 : d ∣ 179 := h6
    have h9 : d ≤ 179 := by
      exact Nat.le_of_dvd (by norm_num) h8
    have h10 : d ≥ 2 := by
      omega
    interval_cases d <;> norm_num at h8 h1 h2 <;> omega
  exact h7