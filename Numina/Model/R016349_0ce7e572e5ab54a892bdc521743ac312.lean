import Mathlib

theorem number_theory_310243 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : q = 4^p + p^4 + 4) :
    p + q = 152 := by
  by_cases h1 : p > 3
  · -- Assume p > 3, then p is a prime greater than 3
    have hp2 : p % 3 = 1 ∨ p % 3 = 2 := by
      have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by
        by_contra h
        push_neg at h
        have : p % 3 = 0 := by omega
        have h4 : p ≠ 3 := by
          omega
        have h5 : ¬Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        tauto
      assumption
    have h2 : q % 3 = 0 := by
      rw [h]
      have h4 : (4 : ℕ) ^ p % 3 = 1 := by
        have h5 : ∀ k : ℕ, (4 : ℕ) ^ (k + 1) % 3 = 1 := by
          intro k
          induction k with
          | zero => norm_num
          | succ k ih =>
            simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
            all_goals omega
        specialize h5 (p - 1)
        have h6 : p - 1 + 1 = p := by omega
        rw [h6] at h5
        assumption
      have h5 : (p ^ 4) % 3 = 1 := by
        rcases hp2 with (h | h)
        · -- p ≡ 1 [MOD 3]
          have : p % 3 = 1 := h
          have h8 : p ^ 4 % 3 = 1 := by
            simp [Nat.pow_mod, this]
          assumption
        · -- p ≡ 2 [MOD 3]
          have : p % 3 = 2 := h
          have h8 : p ^ 4 % 3 = 1 := by
            simp [Nat.pow_mod, this]
          assumption
      omega
    have h3 : q > 3 := by
      have hp1 : p > 3 := h1
      have hp2 : p ≥ 4 := by omega
      have h4 : q ≥ 256 + 256 + 4 := by
        rw [h]
        have h5 : (4 : ℕ) ^ p ≥ (4 : ℕ) ^ 4 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) hp2
        have h6 : p ^ 4 ≥ (4 : ℕ) ^ 4 := by
          have hp7 : p ≥ 4 := by linarith
          have h8 : p ^ 4 ≥ (4 : ℕ) ^ 4 := by
            apply Nat.pow_le_pow_of_le_left hp7 4
          assumption
        omega
      omega
    have h4 : ¬Nat.Prime q := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
      all_goals
        omega
    contradiction
  · -- p ≤ 3
    have hp1 : p ≤ 3 := by linarith
    have hp2 : p ≥ 2 := Nat.Prime.two_le hp
    have h1 : p = 2 ∨ p = 3 := by
      interval_cases p <;> tauto
    rcases h1 with (r | r)
    · -- p = 2
      have hp2 : p = 2 := r
      rw [hp2] at h
      have hq1 : q = 36 := by
        norm_num [h]
      rw [hq1] at hq
      norm_num at hq
    · -- p = 3
      have hp3 : p = 3 := r
      rw [hp3] at h
      have hq1 : q = 149 := by
        norm_num [h]
      omega