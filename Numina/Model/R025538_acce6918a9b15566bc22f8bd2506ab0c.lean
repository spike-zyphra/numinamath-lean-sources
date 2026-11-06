import Mathlib

theorem number_theory_12352 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : q^5 - 2 * p^2 = 1) : p + q = 14 := by 
  have h1 : q^5 = 2 * p^2 + 1 := by
    omega
  by_cases h2 : q % 3 = 0
  · -- If q ≡ 0 (mod 3), then q = 3
    have hq3 : q = 3 := by
      by_cases hq1 : q > 3
      · -- q > 3 and q ≡ 0 (mod 3), so q is not prime
        have hq3 : q % 3 = 0 := h2
        have hqnotprime : ¬q.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
          all_goals omega
        tauto
      · -- q ≤ 3 and q is prime
        interval_cases q <;> try tauto
    rw [hq3] at h1
    have hp11 : p = 11 := by
      nlinarith
    linarith
  · -- q ≡ 1 or 2 (mod 3)
    have h3 : q % 3 = 1 ∨ q % 3 = 2 := by
      omega
    have h8 : q ^ 5 % 3 = q % 3 := by
      rcases h3 with (h21 | h21)
      · -- q ≡ 1 (mod 3)
        simp [pow_succ, Nat.mul_mod, h21]
        all_goals omega
      · -- q ≡ 2 (mod 3)
        simp [pow_succ, Nat.mul_mod, h21]
        all_goals omega
    -- If q ≡ 1 or 2 (mod 3), then p must be 3
    by_cases h22 : p % 3 = 0
    · -- p ≡ 0 (mod 3), so p = 3
      have hp3 : p = 3 := by
        by_cases hp1 : p > 3
        · -- p > 3 and p ≡ 0 (mod 3), so p is not prime
          have hp3 : p % 3 = 0 := h22
          have hpnotprime : ¬p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
            all_goals omega
          tauto
        · -- p ≤ 3 and p is prime
          interval_cases p <;> try tauto
      rw [hp3] at h1
      -- Now q ^ 5 = 19, which is impossible
      have eq : q ^ 5 = 19 := by
        nlinarith
      have q2 : q ≤ 2 := by
        by_contra h
        push_neg at h
        have h11 : q ^ 5 ≥ 3 ^ 5 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals linarith
        nlinarith
      interval_cases q <;> try { contradiction }
      all_goals omega
    · -- p ≡ 1 or 2 (mod 3)
      have h9 : (2 * (p : ℕ) ^ 2 + 1) % 3 = 0 ∨ (2 * (p : ℕ) ^ 2 + 1) % 3 = 1 ∨ (2 * (p : ℕ) ^ 2 + 1) % 3 = 2 := by
        omega
      have h21 : p % 3 = 1 ∨ p % 3 = 2 := by
        omega
      have h10 : (2 * (p : ℕ) ^ 2 + 1) % 3 = 0 := by
        rcases h21 with (h21 | h21)
        · -- p ≡ 1 (mod 3)
          simp [pow_two, Nat.add_mod, Nat.mul_mod, h21]
          all_goals omega
        · -- p ≡ 2 (mod 3)
          simp [pow_two, Nat.add_mod, Nat.mul_mod, h21]
          all_goals omega
      have h11 : (q ^ 5) % 3 = (2 * (p : ℕ) ^ 2 + 1) % 3 := by
        omega
      rw [h10] at h11
      omega