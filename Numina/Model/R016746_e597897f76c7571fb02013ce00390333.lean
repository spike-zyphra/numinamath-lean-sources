import Mathlib

theorem number_theory_4536
  (a b : ℕ)
  (h₀ : a * 8536 = b * 5432)
  (h₁ : Nat.gcd a b = 1) :
  a + b = 18 := by
  have h2 : a * 11 = b * 7 := by
    omega
  have h3 : a = 7 := by
    have h4 : a ∣ 7 * b := by
      use 11
      all_goals 
      omega
    -- Since Nat.Coprime implies no common factors
    have h10 : Nat.gcd a b = 1 := h₁
    -- Show that `a` divides 7
    have h5 : a ∣ 7 := by
      have h6 : a ∣ 7 * b := h4
      have h7 : Nat.Coprime a b := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact h₁
      have h8 : a ∣ 7 := by 
        apply Nat.Coprime.dvd_of_dvd_mul_right h7 h6
      exact h8
    -- Find all divisors of 7, which are {1,7}
    have h6 : a = 1 ∨ a = 7 := by
      have h7 : a ∣ 7 := h5
      have h8 : a ≤ 7 := by
        exact Nat.le_of_dvd (by norm_num) h7
      interval_cases a <;> try { tauto }
    cases h6 with
    | inl ha1 =>
      -- If a = 1, then from a * 11 = b * 7, deduce b ≈ 1
      rw [ha1] at h2
      omega
    | inr ha7 =>
      rw [ha7] at h2
      omega
  -- Now that a = 7 is known, determine b
  have h4 : b = 11 := by
    rw [h3] at h2
    omega
  calc
    a + b = 7 + 11 := by rw [h3, h4]
    _ = 18 := by norm_num