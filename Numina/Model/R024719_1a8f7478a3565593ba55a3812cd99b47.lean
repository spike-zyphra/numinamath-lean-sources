import Mathlib

theorem number_theory_156414 (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ¬∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≥ 10 ∧ q ≥ 10 ∧ r ≥ 10 ∧ p ^ (2 * a) + q ^ b = r ^ (2 * c) := by
  rintro ⟨p, q, r, hp, hq, hr, hp10, hq10, hr10, heq⟩
  have eq1 : p ^ (2 * a) + q ^ b = r ^ (2 * c) := heq

  have eq_mod_3 : (p ^ (2 * a) + q ^ b) % 3 = (r ^ (2 * c)) % 3 := by
    omega

  have eq3 : p % 3 = 1 ∨ p % 3 = 2 := by
    by_contra h
    push_neg at h
    have h4 : p % 3 = 0 := by
      omega
    have h7 : ¬p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
    contradiction

  have eq5 : q % 3 = 1 ∨ q % 3 = 2 := by
    by_contra h
    push_neg at h
    have h4 : q % 3 = 0 := by
      omega
    have h7 : ¬q.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega) (by omega) (by omega)
    contradiction

  have eq7 : r % 3 = 1 ∨ r % 3 = 2 := by
    by_contra h
    push_neg at h
    have h4 : r % 3 = 0 := by
      omega
    have h7 : ¬r.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ r by omega) (by omega) (by omega)
    contradiction

  -- Calculate p^(2*a) mod 3.
  have eq1_mod : (p ^ (2 * a)) % 3 = 1 := by
    have h1 : p % 3 = 1 ∨ p % 3 = 2 := eq3
    rcases h1 with (h1 | h1)
    · -- p ≡ 1 (mod 3)
      simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.pow_mul, Nat.pow_two]
    · -- p ≡ 2 (mod 3)
      simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.pow_mul, Nat.pow_two]

  have eq2_mod : (q ^ b) % 3 = 1 ∨ (q ^ b) % 3 = 2 := by
    have h2 : q % 3 = 1 ∨ q % 3 = 2 := eq5
    rcases h2 with (h2 | h2)
    · -- q ≡ 1 (mod 3)
      have h3 : (q ^ b) % 3 = 1 := by
        simp [Nat.pow_mod, h2]
      omega
    · -- q ≡ 2 (mod 3)
      have h3 : (q ^ b) % 3 = 1 ∨ (q ^ b) % 3 = 2 := by 
        have h4 : q % 3 = 2 := h2
        have : ∀ b : ℕ, (q ^ b) % 3 = 1 ∨ (q ^ b) % 3 = 2 := by 
          intro b
          induction b with 
          | zero =>
            simp [Nat.pow_zero, h4]
          | succ b ih =>
            simp [Nat.pow_succ, Nat.mul_mod, h4] at ih ⊢ 
            omega
        specialize this b
        tauto
      omega

  -- Calculate r^(2*c) mod 3.
  have eq3_mod : (r ^ (2 * c)) % 3 = 1 := by
    have h3 : r % 3 = 1 ∨ r % 3 = 2 := eq7
    rcases h3 with (h3 | h3)
    · -- r ≡ 1 (mod 3)
      simp [Nat.pow_mod, h3, Nat.mul_mod, Nat.pow_mul, Nat.pow_two]
    · -- r ≡ 2 (mod 3)
      simp [Nat.pow_mod, h3, Nat.mul_mod, Nat.pow_mul, Nat.pow_two]

  -- Derive contradiction from the equations.
  omega