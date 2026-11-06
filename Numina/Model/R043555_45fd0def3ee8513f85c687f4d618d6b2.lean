import Mathlib

theorem number_theory_4581 (a b : ℕ) (hab : 0 < a ∧ 0 < b) :
    gcd a b ∣ lcm a b ∧ ((gcd a b = lcm a b) ↔ a = b) := by
  constructor
  · -- Prove that gcd a b divides lcm a b.
    have h1 : 0 < a := hab.1
    have h2 : 0 < b := hab.2
    have h3 : gcd a b ∣ a := Nat.gcd_dvd_left a b
    have h4 : a ∣ lcm a b := Nat.dvd_lcm_left a b
    have h5 : gcd a b ∣ lcm a b := by
      exact dvd_trans h3 h4
    exact h5
  · -- Prove that gcd a b = lcm a b ↔ a = b
    constructor
    · -- Forward: if gcd a b = lcm a b, then a = b
      intro h_eq
      have h1 : 0 < a := hab.1
      have h2 : 0 < b := hab.2
      have h3 : gcd a b * lcm a b = a * b := Nat.gcd_mul_lcm a b
      rw [show lcm a b = gcd a b by omega] at h3
      have h4 : gcd a b ^ 2 = a * b := by 
        nlinarith
      have h5 : gcd a b ∣ a := by
        exact Nat.gcd_dvd_left a b
      have h6 : gcd a b ∣ b := by
        exact Nat.gcd_dvd_right a b
      rcases h5 with ⟨k, hk⟩
      rcases h6 with ⟨m, hm⟩
      have h7 : k * m = 1 := by
        rw [hk, hm] at h4
        nlinarith
      have h8 : k = 1 := by
        have h77 : k * m = 1 := h7
        have : k ∣ 1 := by
          use m
          all_goals linarith
        have h9 : k ≤ 1 := by
          exact Nat.le_of_dvd (by norm_num) this
        interval_cases k <;> omega
      have h9 : m = 1 := by
        have h77 : k * m = 1 := h7
        have h88 : k = 1 := h8
        rw [h88] at h77
        omega
      have h7 : a = gcd a b := by
        nlinarith
      have h8 : b = gcd a b := by
        nlinarith
      have h9 : a = b := by
        omega
      exact h9
    · -- Backward: if a = b, then gcd a b = lcm a b
      intro h_eq
      rw [show b = a by omega]
      have h3 : gcd a a = a := by
        simp [Nat.gcd_self]
      have h4 : lcm a a = a := by
        simp [Nat.lcm_self]
      rw [h3, h4]
      all_goals nlinarith