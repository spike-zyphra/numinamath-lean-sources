import Mathlib

theorem algebra_254336 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcoprime : Nat.Coprime a b) (hdiv : a + b ∣ a^4 + b^4) :
    a = 1 ∧ b = 1 := by
  have h1 : (a + b : ℤ) ∣ 2 * (a : ℤ) ^ 4 := by
    have h2 : (a + b : ℤ) ∣ (a : ℤ) ^ 4 + (b : ℤ) ^ 4 := by
      exact_mod_cast hdiv
    have h3 : (a + b : ℤ) ∣ (a : ℤ) ^ 4 - (b : ℤ) ^ 4 := by
      use ((a : ℤ) - (b : ℤ)) * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2)
      ring_nf
    have h4 : (a + b : ℤ) ∣ ((a : ℤ) ^ 4 + (b : ℤ) ^ 4) + ((a : ℤ) ^ 4 - (b : ℤ) ^ 4) := by
      apply dvd_add h2 h3
    have h5 : ((a : ℤ) ^ 4 + (b : ℤ) ^ 4) + ((a : ℤ) ^ 4 - (b : ℤ) ^ 4) = 2 * (a : ℤ) ^ 4 := by
      ring
    rw [h5] at h4
    exact_mod_cast h4
  have h2 : (a + b : ℤ) ∣ 2 * (b : ℤ) ^ 4 := by
    have h2 : (a + b : ℤ) ∣ (a : ℤ) ^ 4 + (b : ℤ) ^ 4 := by
      exact_mod_cast hdiv
    have h3 : (a + b : ℤ) ∣ (b : ℤ) ^ 4 - (a : ℤ) ^ 4 := by
      use ((b : ℤ) - (a : ℤ)) * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2)
      ring_nf
    have h4 : (a + b : ℤ) ∣ ((a : ℤ) ^ 4 + (b : ℤ) ^ 4) + ((b : ℤ) ^ 4 - (a : ℤ) ^ 4) := by
      apply dvd_add h2 h3
    have h5 : ((a : ℤ) ^ 4 + (b : ℤ) ^ 4) + ((b : ℤ) ^ 4 - (a : ℤ) ^ 4) = 2 * (b : ℤ) ^ 4 := by
      ring
    rw [h5] at h4
    exact_mod_cast h4
  have h3 : (a + b : ℤ) ∣ 2 := by
    have h4 : (a + b : ℤ) ∣ 2 * (a : ℤ) ^ 4 := h1
    have h5 : (a + b : ℤ) ∣ 2 * (b : ℤ) ^ 4 := h2
    have h6 : (a + b : ℤ) ∣ Nat.gcd (2 * a ^ 4) (2 * b ^ 4) := by
      apply Int.dvd_gcd h4 h5
    have h7 : Nat.gcd (2 * a ^ 4) (2 * b ^ 4) = 2 := by
      have h8 : Nat.gcd (a ^ 4) (b ^ 4) = 1 := by
        exact Nat.Coprime.pow 4 4 hcoprime
      have h9 : Nat.gcd (2 * a ^ 4) (2 * b ^ 4) = 2 * Nat.gcd (a ^ 4) (b ^ 4) := by
        rw [Nat.gcd_mul_left]
        all_goals norm_num
        all_goals omega
      rw [h9, h8]
      all_goals norm_num
    have h8 : (Nat.gcd (2 * a ^ 4) (2 * b ^ 4) : ℤ) = 2 := by
      exact_mod_cast h7
    have h10 : (a + b : ℤ) ∣ (2 : ℤ) := by
      rw [h8] at h6
      exact_mod_cast h6
    exact_mod_cast h10
  have h4 : (a + b) ∣ 2 := by
    exact_mod_cast h3
  have h5 : (a + b) = 1 ∨ (a + b) = 2 := by
    have h6 : (a + b) ∣ 2 := h4
    have h8 : (a + b) ≤ 2 := by
      exact Nat.le_of_dvd (show 0 < 2 by norm_num) h6
    have h9 : (a + b) ≥ 2 := by
      have ha1 : a ≥ 1 := by 
        omega 
      have hb1 : b ≥ 1 := by
        omega 
      omega
    interval_cases (a + b) <;> try { tauto }
  cases h5 with
  | inl h => 
    omega
  | inr h => 
    have h11 : a = 1 := by
      have h12 : a ≤ 2 := by
        omega
      have h13 : a ≥ 1 := by 
        omega
      interval_cases a <;> omega
    have h12 : b = 1 := by
      have h13 : b ≤ 2 := by
        omega
      have h14 : b ≥ 1 := by 
        omega
      interval_cases b <;> omega
    exact ⟨h11, h12⟩