import Mathlib

theorem number_theory_7444 (a b c : ℕ) (habc : 0 < a ∧ 0 < b ∧ 0 < c)
    (hab : a / Nat.gcd a b ∣ c) : a ∣ b * c := by
  have h1 : a / Nat.gcd a b ∣ c := hab
  have h2 : Nat.gcd a b ∣ a := by
    apply Nat.gcd_dvd_left
  have h3 : Nat.gcd a b ∣ b := by
    apply Nat.gcd_dvd_right
  have h7 : Nat.gcd a b ∣ b := by
    apply Nat.gcd_dvd_right
  have h8 : a / Nat.gcd a b ∣ c := h1
  have h9 : a ∣ b * c := by
    -- We have `h1 : a / Nat.gcd a b ∣ c`
    -- and `h7 : Nat.gcd a b ∣ b`
    -- From these we can derive divisibility
    have h10 : (a / Nat.gcd a b) * (Nat.gcd a b) ∣ (c * b) := by
      apply Nat.mul_dvd_mul
      exact h1
      exact h7
    have h11 : (a / Nat.gcd a b) * (Nat.gcd a b) = a := by
      have h2' : Nat.gcd a b ≠ 0 := by
        have h3 : a > 0 := habc.1
        have h4 : b > 0 := habc.2.1
        have h5 : Nat.gcd a b > 0 := by
          apply Nat.gcd_pos_of_pos_left
          exact h3
        omega
      have h12 : (a / Nat.gcd a b) * (Nat.gcd a b) = a := by
        have h13 : a = (a / Nat.gcd a b) * (Nat.gcd a b) := by
          rw [Nat.div_mul_cancel]
          have h4' : Nat.gcd a b ∣ a := by
            apply Nat.gcd_dvd_left
          exact h4'
        linarith
      linarith
    have h17 : a ∣ c * b := by
      rw [show (a / Nat.gcd a b) * (Nat.gcd a b) = a by exact h11] at h10
      exact_mod_cast h10
    -- Derive divisibility for b * c
    have h18 : a ∣ b * c := by
      have h19 : b * c = c * b := by ring 
      rw [h19] 
      exact_mod_cast h17
    exact h18
  exact h9