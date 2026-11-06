import Mathlib

theorem number_theory_168277 {n : ℕ} (hn : n ≠ 1) (h : 319 % n = 0 ∧ 232 % n = 0) :
    n = 29 := by
  have h1 : 319 % n = 0 := h.1
  have h2 : 232 % n = 0 := h.2
  have h3 : n ∣ 319 := by 
    exact Nat.dvd_of_mod_eq_zero h1
  have h4 : n ∣ 232 := by 
    exact Nat.dvd_of_mod_eq_zero h2
  have h5 : n ∣ 29 := by 
    exact Nat.dvd_gcd h3 h4
  have h6 : n = 29 ∨ n = 1 := by 
    have h7 : n ∣ 29 := h5
    have h8 : n ≤ 29 := by 
      exact Nat.le_of_dvd (by norm_num) h7
    interval_cases n <;> tauto
  cases h6 with
  | inl h7 =>
    exact h7
  | inr h8 =>
    exfalso
    exact hn h8