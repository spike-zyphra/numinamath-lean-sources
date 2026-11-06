import Mathlib
open Nat

theorem number_theory_600011 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
  (p ^ q + 1).Prime ↔ p = 2 ∧ q = 2 := by
  constructor
  · -- Assume (p ^ q + 1) is prime, prove p = 2 ∧ q = 2
    intro h
    by_cases h1 : p % 2 = 1
    · -- Assume p is odd
      by_cases h3 : q % 2 = 1
      · -- Assume q is odd
        have h4 : q % 2 = 1 := h3
        have h5 : p > 2 := by
          by_contra h
          push_neg at h
          interval_cases p <;> norm_num at hp h1 ⊢
        have h6 : q > 2 := by
          by_contra h
          push_neg at h
          interval_cases q <;> norm_num at hq h4 ⊢
        have h7 : p % 2 = 1 := h1
        have h8 : (p ^ q) % 2 = 1 := by
          have h9 : p % 2 = 1 := h1
          have h10 : ∀ (k : ℕ), p ^ (k + 1) % 2 = 1 := by
            intro k
            induction k with
            | zero =>
              simp [h9]
            | succ k ih =>
              simp [Nat.pow_add, Nat.pow_one, Nat.mul_mod, h9] at ih ⊢
              all_goals omega
          specialize h10 (q - 1)
          have h11 : q - 1 + 1 = q := by
            omega
          rw [h11] at h10
          omega
        have h9 : (p ^ q + 1) % 2 = 0 := by
          omega
        have h11 : (p ^ q + 1) > 2 := by
          have h12 : p ≥ 3 := by
            omega
          have h13 : q ≥ 3 := by
            omega
          have h14 : p ^ q ≥ p ^ 3 := by
            have h15 : q ≥ 3 := h13
            have h16 : p ≥ 3 := h12
            have h17 : p ^ q ≥ p ^ 3 := by
              apply Nat.pow_le_pow_of_le_right
              all_goals omega
            linarith
          have h15 : p ^ 3 ≥ 27 := by
            have h16 : p ≥ 3 := h12
            have h17 : p ^ 3 ≥ 3 ^ 3 := by
              apply Nat.pow_le_pow_left
              all_goals omega
            norm_num at h17 ⊢
            linarith
          have h18 : p ^ q ≥ 27 := by
            linarith [h14, h15]
          omega
        have h10 : ¬ (p ^ q + 1).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (p ^ q + 1) by omega)
          all_goals
            omega
        contradiction
      · -- Assume q is even
        have h4 : q % 2 = 0 := by
          omega
        have h5 : q = 2 := by
          by_cases h6 : q > 2
          · -- Assume q > 2
            have h7 : ¬q.Prime := by
              apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
              all_goals omega
            contradiction
          · -- Assume q ≤ 2
            interval_cases q <;> norm_num at hq h4 ⊢
        rw [h5] at h
        have h7 : (p ^ 2 + 1) % 2 = 0 := by
          have h8 : p % 2 = 1 := h1
          have h9 : p ^ 2 % 2 = 1 := by
            simp [Nat.pow_mod, h8]
          omega
        have h11 : (p ^ 2 + 1) > 2 := by
          have h12 : p ≥ 3 := by
            by_contra h
            push_neg at h
            interval_cases p <;> norm_num at hp h1 ⊢
          have h13 : p ^ 2 ≥ 9 := by
            nlinarith
          omega
        have h10 : ¬(p ^ 2 + 1).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (p ^ 2 + 1) by omega)
          all_goals
            omega
        have h11 : (p ^ 2 + 1).Prime := by
          simpa [h5] using h
        contradiction
    · -- Assume p is even
      have h2 : p % 2 = 0 := by
        omega
      have h3 : p = 2 := by
        by_cases h4 : p > 2
        · -- Assume p > 2
          have h5 : ¬p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
            all_goals omega
          contradiction
        · -- Assume p ≤ 2
          interval_cases p <;> norm_num at hp ⊢
      rw [h3] at h
      by_cases h1 : q % 2 = 1
      · -- Assume q is odd
        have h4 : q % 2 = 1 := h1
        have h5 : q > 2 := by
          by_contra h
          push_neg at h
          interval_cases q <;> norm_num at hq h4 ⊢
        have h6 : (2 ^ q + 1) % 3 = 0 := by
          have h7 : q % 2 = 1 := h1
          have h8 : ∃k, q = 2 * k + 1 := by
            refine' ⟨q / 2, by omega⟩
          rcases h8 with ⟨k, hk⟩
          rw [hk]
          have h9 : (2 ^ (2 * k + 1) : ℕ) % 3 = 2 := by
            have h10 : ∀ (k : ℕ), (2 ^ (2 * k + 1) : ℕ) % 3 = 2 := by
              intro k
              induction k with
              | zero =>
                norm_num
              | succ k ih =>
                simp [Nat.pow_succ, Nat.pow_mul, Nat.mul_mod] at ih ⊢
                all_goals omega
            specialize h10 k
            simpa using h10
          omega
        have h7 : ¬(2 ^ q + 1).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2 ^ q + 1) by omega)
          all_goals
            -- Show that 3 divides it and it's greater 3
            have h8 : (2 ^ q + 1) > 3 := by
              have h9 : q ≥ 3 := by
                by_contra h
                push_neg at h
                interval_cases q <;> norm_num at hq h1 ⊢
              have h10 : 2 ^ q ≥ 8 := by
                have h11 : q ≥ 3 := h9
                have h12 : 2 ^ q ≥ 2 ^ 3 := by
                  apply Nat.pow_le_pow_of_le_right (by linarith) h11
                norm_num at h12 ⊢
                all_goals linarith
              omega
            all_goals omega
        contradiction
      · -- Assume q is even
        have h4 : q % 2 = 0 := by
          omega
        have h5 : q = 2 := by
          by_cases h6 : q > 2
          · -- Assume q > 2
            have h7 : ¬q.Prime := by
              apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
              all_goals omega
            contradiction
          · -- Assume q ≤ 2
            interval_cases q <;> norm_num at hq h4 ⊢
        exact ⟨by omega, by omega⟩
  · -- Assume p = 2 ∧ q = 2, prove (p ^ q + 1) is prime
    rintro ⟨rfl, rfl⟩
    norm_num