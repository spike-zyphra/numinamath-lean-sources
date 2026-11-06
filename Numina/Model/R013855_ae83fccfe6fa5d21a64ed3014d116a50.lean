import Mathlib

theorem number_theory_115304 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    2^(2*p) - 2^p + 1 = q ↔ (p = 2 ∧ q = 13) := by
  constructor
  · -- Assume 2^(2*p) - 2^p + 1 = q, prove p = 2 ∧ q = 13
    intro h
    have h1 : p ≥ 2 := Nat.Prime.two_le hp
    have h2 : q ≥ 2 := Nat.Prime.two_le hq
    by_cases hp2 : p = 2
    · -- p = 2
      rw [hp2] at h
      have h3 : q = 13 := by
        have h4 : 2 ^ (2 * 2) - 2 ^ 2 + 1 = 16 - 4 + 1 := by norm_num
        have h5 : 16 - 4 + 1 = 13 := by norm_num
        omega
      exact ⟨by simp [hp2], by omega⟩
    · -- p ≠ 2, so p must be odd
      have hp3 : p > 2 := by
        by_contra h
        push_neg at h
        interval_cases p <;> try { contradiction }
        all_goals tauto
      have hp5 : p % 2 = 1 := by
        have h1 : p > 2 := hp3
        have h2 : p % 2 = 1 := by
          by_contra h
          push_neg at h
          have h3 : p % 2 = 0 := by omega
          have h4 : ¬ p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
            all_goals omega
          contradiction
        assumption
      have h3 : q % 3 = 0 := by
        have h4 : (2 : ℕ) ^ (2 * p) % 3 = 1 := by
          have h5 : ∀ k : ℕ, (2 : ℕ) ^ (2 * (2 * k + 1)) % 3 = 1 := by
            intro k
            induction k with
            | zero =>
              norm_num
            | succ k ih =>
              simp [Nat.pow_succ, Nat.mul_add] at ih ⊢
              all_goals norm_num at ih ⊢
              all_goals omega
          have : ∃ k : ℕ, p = 2 * k + 1 := by
            have hp5' : p % 2 = 1 := hp5
            have : p > 0 := by omega
            have hp5'' : p = 2 * (p / 2) + 1 := by omega
            use p / 2
            all_goals linarith
          rcases this with ⟨k, hk⟩
          rw [show 2 * p = 2 * (2 * k + 1) by rw [hk]; all_goals omega]
          apply h5 k
        have h5 : (2 : ℕ) ^ p % 3 = 2 := by
          have h6 : ∀ k : ℕ, (2 : ℕ) ^ (2 * k + 1) % 3 = 2 := by
            intro k
            induction k with
            | zero =>
              norm_num
            | succ k ih =>
              simp [Nat.pow_succ, Nat.mul_add] at ih ⊢
              all_goals norm_num at ih ⊢
              all_goals omega
          have : ∃ k : ℕ, p = 2 * k + 1 := by
            have hp5' : p % 2 = 1 := hp5
            have : p > 0 := by omega
            have hp5'' : p = 2 * (p / 2) + 1 := by omega
            use p / 2
            all_goals linarith
          rcases this with ⟨k, hk⟩
          rw [show p = 2 * k + 1 by linarith]
          apply h6 k
        omega
      have h3' : q = 3 := by
        have h3 : q % 3 = 0 := h3
        have h4 : q.Prime := hq
        have h5 : q = 3 := by
          by_cases h6 : q > 3
          · -- Assume q > 3, need to derive contradiction
            have h7 : ¬ q.Prime := by
              apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
              all_goals omega
            contradiction
          · -- q ≤ 3
            interval_cases q <;> tauto
        assumption
      rw [h3'] at h
      have h4 : 2 ^ (2 * p) - 2 ^ p + 1 = 3 := by
        linarith [h]
      have h5 : p ≥ 3 := hp3
      have h6 : 2 ^ (2 * p) = 2 ^ p + 2 := by
        omega
      have h7 : p ≥ 3 := h5
      have h8 : 2 ^ (2 * p) = (2 ^ p) ^ 2 := by 
        ring_nf
      rw [h8] at h6
      have h9 : (2 ^ p) ^ 2 = 2 ^ p + 2 := by
        omega
      have h10 : 2 ^ p ≥ 8 := by
        have h11 : p ≥ 3 := h7
        have h12 : 2 ^ p ≥ 2 ^ 3 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) h11
        norm_num at h12 ⊢
        all_goals linarith
      nlinarith
  · -- Assume p = 2 ∧ q = 13, prove 2^(2*p) - 2^p + 1 = q
    rintro ⟨hp2, hq13⟩
    rw [hp2, hq13]
    all_goals norm_num