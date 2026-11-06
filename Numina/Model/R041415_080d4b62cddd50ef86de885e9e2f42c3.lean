import Mathlib

theorem number_theory_228111 (p : ℕ) (hp : p.Prime) :
    IsSquare (5^p + 12^p) ↔ p = 2 := by
  constructor
  · -- Assume 5^p + 12^p is a perfect square, prove p = 2
    intro h
    by_cases h1 : p > 2
    · -- p > 2
      have h2 : p % 2 = 1 := by
        by_contra h'
        push_neg at h'
        have h3 : p % 2 = 0 := by
          omega
        have h4 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals omega
        tauto
      -- Assume $5^p + 12^p$ is a perfect square, prove p = 2.
      -- Looking at modulo 3.
      -- 5 ≡ 2 ≡ -1 (mod 3)
      -- 12 ≡ 0 (mod 3)
      -- So $5^p + 12^p ≡ (-1)^p + 0 ≡ (-1)^p$ (mod 3)
      -- If p is odd, then (-1)^p = -1 ≡ 2 (mod 3)
      -- But a perfect square modulo 3 is 0 or 1.
      have h3 : p % 2 = 1 := h2
      have h4 : (5 ^ p + 12 ^ p : ℕ) % 3 = 2 := by
        have h6 : ∃ k : ℕ, p = 2 * k + 1 := by
          have h6 : p % 2 = 1 := h3
          have h7 : ∃ k, p = 2 * k + 1 := by
            refine' ⟨p / 2, by omega⟩
          tauto
        rcases h6 with ⟨k, hk⟩
        have h7 : (5 : ℕ) ^ p % 3 = 2 := by
          rw [show p = 2 * k + 1 by omega]
          have h5 : ∀ k : ℕ, (5 ^ (2 * k + 1) : ℕ) % 3 = 2 := by
            intro k
            induction k with
            | zero =>
              norm_num
            | succ k ih =>
              simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
              all_goals omega
          specialize h5 k
          simpa using h5
        have h8 : (12 : ℕ) ^ p % 3 = 0 := by
          have h9 : p ≥ 1 := by
            linarith
          have h10 : ∀ (k : ℕ), k ≥ 1 → (12 : ℕ) ^ k % 3 = 0 := by
            intro k hk
            induction k with
            | zero =>
              linarith
            | succ k ih =>
              cases k with
              | zero =>
                norm_num
              | succ k =>
                simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
                all_goals omega
          specialize h10 p (by linarith)
          simpa using h10
        omega
      rcases h with ⟨r, hr⟩
      have h8 : (r : ℕ) ^ 2 % 3 = 0 ∨ (r : ℕ) ^ 2 % 3 = 1 := by
        have h1 : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by
          omega
        rcases h1 with (h1 | h1 | h1)
        · -- r ≡ 0 (mod 3)
          simp [Nat.pow_mod, h1]
        · -- r ≡ 1 (mod 3)
          simp [Nat.pow_mod, h1]
        · -- r ≡ 2 (mod 3)
          simp [Nat.pow_mod, h1]
      have h9 : (r : ℕ) ^ 2 = 5 ^ p + 12 ^ p := by
        linarith [hr]
      have h10 : (r : ℕ) ^ 2 % 3 = 2 := by
        omega
      omega
    · -- p ≤ 2, since it's prime, so p = 2.
      have h1 : p = 2 := by
        interval_cases p <;> tauto
      tauto
  · -- Assume p = 2, prove that 5^p + 12^p is a perfect square.
    intro h
    rw [h]
    use 13
    all_goals norm_num