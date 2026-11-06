import Mathlib

theorem number_theory_149173 (n : ℕ) (hn : Even n) (h : 6 < n) :
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Coprime (n - p) (n - q) := by
  have h2 : n > 6 := by linarith
  use 3, 5
  constructor
  · -- Show that 3 is prime
    norm_num
  constructor
  · -- Show that 5 is prime
    norm_num
  · -- Show that (n - 3) and (n - 5) are coprime
    have h3 : n % 2 = 0 := by
      obtain ⟨k, hk⟩ := hn
      omega
    have h4 : n ≥ 7 := by
      omega
    have h5 : n ≥ 8 := by
      by_contra h8
      push_neg at h8
      have : n < 8 := by linarith
      omega
    have h6 : Nat.Coprime (n - 3) (n - 5) := by
      have h8 : n % 2 = 0 := h3
      have h9 : (n - 3) % 2 = 1 := by
        omega
      have h10 : (n - 5) % 2 = 1 := by
        omega
      have h14 : (n - 3 : ℕ) ≥ 1 := by
        omega
      have h15 : (n - 5 : ℕ) ≥ 1 := by
        omega
      have h13 : Nat.gcd (n - 3) (n - 5) = 1 := by
        have h14 : Nat.gcd (n - 3) (n - 5) ∣ (n - 3) := by
          exact Nat.gcd_dvd_left (n - 3) (n - 5)
        have h15 : Nat.gcd (n - 3) (n - 5) ∣ (n - 5) := by
          exact Nat.gcd_dvd_right (n - 3) (n - 5)
        have h16 : Nat.gcd (n - 3) (n - 5) ∣ ((n - 3) - (n - 5)) := by
          apply Nat.dvd_sub'
          · exact h14
          · exact h15
        have h17 : ((n - 3) : ℕ) - ((n - 5) : ℕ) = 2 := by
          omega
        have h18 : Nat.gcd (n - 3) (n - 5) ∣ 2 := by
          rw [h17] at h16
          exact h16
        have h19 : Nat.gcd (n - 3) (n - 5) = 1 ∨ Nat.gcd (n - 3) (n - 5) = 2 := by
          have h1 : Nat.gcd (n - 3) (n - 5) ∣ 2 := h18
          have h2 : Nat.gcd (n - 3) (n - 5) ≤ 2 := by
            exact Nat.le_of_dvd (show 0 < 2 by norm_num) h1
          interval_cases (Nat.gcd (n - 3) (n - 5)) <;> tauto
        rcases h19 with (h19 | h19)
        · -- Case where gcd = 1
          omega
        · -- Case where gcd = 2
          -- This leads to a contradiction since n-3 and n-5 are odd
          have h21 : (n - 3 : ℕ) % 2 = 1 := h9
          have h22 : (n - 3 : ℕ) % 2 = 0 := by
            have h14' : (n - 3) % 2 = 0 := by
              rw [show Nat.gcd (n - 3) (n - 5) = 2 by omega] at h14
              have h14 : 2 ∣ (n - 3) := by
                exact h14
              exact Nat.dvd_iff_mod_eq_zero.mp h14
            omega
          omega
      exact h13
    exact h6