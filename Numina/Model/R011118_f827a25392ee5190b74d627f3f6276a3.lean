import Mathlib

open Nat

theorem number_theory_97032 (m n r s : ℕ) (hm : 0 < m) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s) (hdiv : 702 % m = r ∧ 787 % m = r ∧ 855 % m = r) (hdiv' : 412 % n = s ∧ 722 % n = s ∧ 815 % n = s) : m + n + r + s = 62 := by
  rcases hdiv with ⟨h1, h2, h3⟩
  rcases hdiv' with ⟨h4, h5, h6⟩
  have h7 : m ∣ 85 := by
    have h8 : 787 % m = r := h2
    have h9 : 702 % m = r := h1
    have h10 : (787 : ℕ) % m = (702 : ℕ) % m := by
      rw [h8]
      rw [h9]
    have h11 : m ∣ (787 : ℕ) - (702 : ℕ) := by
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h10)
    have h12 : (787 : ℕ) - (702 : ℕ) = 85 := by
      norm_num
    rw [h12] at h11
    exact h11
  have h8 : m ∣ 68 := by
    have h9 : 855 % m = r := h3
    have h10 : 787 % m = r := h2
    have h11 : (855 : ℕ) % m = (787 : ℕ) % m := by
      rw [h9]
      rw [h10]
    have h12 : m ∣ (855 : ℕ) - (787 : ℕ) := by
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h11)
    have h13 : (855 : ℕ) - (787 : ℕ) = 68 := by
      norm_num
    rw [h13] at h12
    exact h12
  have h9 : m ∣ 17 := by
    exact Nat.dvd_gcd h7 h8
  have h10 : m = 1 ∨ m = 17 := by
    have h11 : m ∣ 17 := h9
    have h12 : m ≤ 17 := by
      exact Nat.le_of_dvd (by linarith) h11
    interval_cases m <;> try { tauto }
  rcases h10 with (h11 | h12)
  · -- m = 1
    have h13 : m = 1 := h11
    have h14 : r = 0 := by
      rw [h13] at h1
      omega
    rw [h14] at hr
    linarith
  · -- m = 17
    have h13 : m = 17 := h12
    have h14 : r = 5 := by
      rw [h13] at h1
      omega
    have h15 : n ∣ 310 := by
      have h16 : 722 % n = s := h5
      have h17 : 412 % n = s := h4
      have h18 : (722 : ℕ) % n = (412 : ℕ) % n := by
        rw [h16]
        rw [h17]
      have h19 : n ∣ (722 : ℕ) - (412 : ℕ) := by
        exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h18)
      have h20 : (722 : ℕ) - (412 : ℕ) = 310 := by
        norm_num
      rw [h20] at h19
      exact h19
    have h16 : n ∣ 93 := by
      have h17 : 815 % n = s := h6
      have h18 : 722 % n = s := h5
      have h19 : (815 : ℕ) % n = (722 : ℕ) % n := by
        rw [h17]
        rw [h18]
      have h20 : n ∣ (815 : ℕ) - (722 : ℕ) := by
        exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h19)
      have h21 : (815 : ℕ) - (722 : ℕ) = 93 := by
        norm_num
      rw [h21] at h20
      exact h20
    have h17 : n ∣ 31 := by
      exact Nat.dvd_gcd h15 h16
    have h18 : n = 1 ∨ n = 31 := by
      have h19 : n ∣ 31 := h17
      have h20 : n ≤ 31 := by
        exact Nat.le_of_dvd (by linarith) h19
      interval_cases n <;> try { tauto }
    rcases h18 with (h19 | h20)
    · -- n = 1
      have h21 : n = 1 := h19
      have h22 : s = 0 := by
        rw [h21] at h4
        omega
      rw [h22] at hs
      linarith
    · -- n = 31
      have h21 : n = 31 := h20
      have h22 : s = 9 := by
        rw [h21] at h4
        omega
      have h23 : m = 17 := h13
      have h24 : r = 5 := h14
      have h25 : n = 31 := h21
      have h26 : s = 9 := h22
      linarith