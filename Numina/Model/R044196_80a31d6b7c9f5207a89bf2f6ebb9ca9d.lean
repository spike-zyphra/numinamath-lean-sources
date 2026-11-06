import Mathlib

theorem number_theory_217417 {a b : ℕ} (_ : 0 < a) (hb : 0 < b)
    (h : Nat.gcd a b + Nat.lcm a b = a + b) :
    a ∣ b ∨ b ∣ a := by
  have h1 : a.gcd b * (a.lcm b) = a * b := by
    rw [Nat.gcd_mul_lcm a b]

  have h2 : a.gcd b + a.lcm b = a + b := by
    linarith

  have h4 : a.gcd b ≤ a := by
    apply Nat.gcd_le_left
    all_goals omega

  have h5 : a.gcd b ≤ b := by
    apply Nat.gcd_le_right
    all_goals omega

  have h8 : a.gcd b * ((a + b) - a.gcd b) = a * b := by
    have h9 : a.lcm b = (a + b) - a.gcd b := by
      omega
    rw [h9] at h1
    omega

  have h19 : (a.gcd b : ℕ) = a ∨ (a.gcd b : ℕ) = b := by
    by_cases h25 : (a.gcd b : ℕ) < a
    · 
      by_cases h26 : (a.gcd b : ℕ) < b
      · 
        exfalso
        nlinarith [sq_nonneg ((a.gcd b : ℕ) : ℕ), sq_nonneg ((a : ℕ) - (a.gcd b : ℕ)), sq_nonneg ((b : ℕ) - (a.gcd b : ℕ)), mul_nonneg (show (0 : ℕ) ≤ a by omega) (show (0 : ℕ) ≤ b by omega)]
      · 
        have h27 : (a.gcd b : ℕ) ≥ (b : ℕ) := by
          omega
        have h28 : (a.gcd b : ℕ) = (b : ℕ) := by
          have h39 : (a.gcd b : ℕ) ≤ (b : ℕ) := h5
          omega
        right
        omega
    · 
      have h25' : (a.gcd b : ℕ) ≥ (a : ℕ) := by
        omega
      by_cases h26 : (a.gcd b : ℕ) < b
      · 
        have h27 : (a.gcd b : ℕ) ≥ (a : ℕ) := by
          omega
        have h28 : (a.gcd b : ℕ) = (a : ℕ) := by
          have h39 : (a.gcd b : ℕ) ≤ (a : ℕ) := h4
          omega
        left
        omega
      · 
        have h27 : (a.gcd b : ℕ) ≥ (b : ℕ) := by
          omega
        have h28 : (a.gcd b : ℕ) = (b : ℕ) := by
          have h39 : (a.gcd b : ℕ) ≤ (b : ℕ) := h5
          omega
        right
        omega

  cases h19 with
  | inl h20 =>
    have h30 : a ∣ b := by
      have h31 : a.gcd b ∣ b := by
        exact Nat.gcd_dvd_right a b
      have h32 : a.gcd b = a := by
        omega
      rw [h32] at h31
      exact h31
    left
    exact h30
  | inr h21 =>
    have h30 : b ∣ a := by
      have h31 : a.gcd b ∣ a := by
        exact Nat.gcd_dvd_left a b
      have h32 : a.gcd b = b := by
        omega
      rw [h32] at h31
      exact h31
    right
    exact h30