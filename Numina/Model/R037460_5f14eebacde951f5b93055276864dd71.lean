import Mathlib

open Nat

theorem number_theory_60123 : IsGreatest {n : ℕ | 0 < n ∧ 2018 % n = 106 % n ∧ 106 % n = 614 % n} 4 := by
  constructor
  · -- Show 4 is in the set
    constructor
    · norm_num  -- proof 4 > 0
    constructor
    · norm_num  -- proof 2018 % 4 = 106 % 4
    · norm_num  -- proof 106 % 4 = 614 % 4
  · -- Show that n ≤ 4 for all n in the set
    intro n hn
    rcases hn with ⟨hn_pos, h1, h2⟩
    have h3 : n ∣ 1912 := by 
      have h1' : 2018 % n = 106 % n := h1
      have h4 : (2018 : ℕ) % n = (106 : ℕ) % n := by
        omega 
      have h5 : n ∣ (2018 : ℕ) - (106 : ℕ) := by
        exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h4)
      have hx1 : (2018 : ℕ) - (106 : ℕ) = (1912 : ℕ) := by omega
      rw [hx1] at h5
      exact h5
    have h4 : n ∣ 508 := by 
      have h2' : 106 % n = 614 % n := h2
      have h6 : (614 : ℕ) % n = (106 : ℕ) % n := by
        omega 
      have h7 : n ∣ (614 : ℕ) - (106 : ℕ) := by
        exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h6)
      have hx2 : (614 : ℕ) - (106 : ℕ) = (508 : ℕ) := by omega
      rw [hx2] at h7 
      exact h7
    have h5 : n ∣ 4 := by
      exact Nat.dvd_gcd h3 h4
    have h6 : n ≤ 4 := by 
      exact Nat.le_of_dvd (by linarith) h5
    omega