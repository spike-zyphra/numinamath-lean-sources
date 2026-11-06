import Mathlib

theorem number_theory_151668 (n : ℕ) :
    5 ∣ (∑ i in Finset.Icc 1 4, i^n) ↔ ¬4 ∣ n := by
  have h1 : ∀ n : ℕ, ∑ i in Finset.Icc 1 4, i ^ n = 1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n := by
    intro n
    simp [Finset.sum_Icc_succ_top, add_assoc]
  rw [h1 n]
  constructor
  · -- Assume that $5$ divides $1^n + 2^n + 3^n + 4^n$, prove $\neg (4$ divides $n)$
    intro h
    by_contra h2
    -- Assume that $4$ divides $n$, prove contradiction
    have h3 : 4 ∣ n := by
      simpa using h2
    rcases h3 with ⟨k, hk⟩
    have h4 : (1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n : ℕ) % 5 = 4 := by
      have h5 : n = 4 * k := by
        omega
      rw [h5]
      have h6 : ∀ k : ℕ, (1 ^ (4 * k) + 2 ^ (4 * k) + 3 ^ (4 * k) + 4 ^ (4 * k) : ℕ) % 5 = 4 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
          all_goals
            norm_num at ih ⊢
            omega
      exact h6 k
    omega
  · -- Assume that $\neg4 \mid n$, prove $5 \mid \sum_{i=1}^4 i^n$
    intro h2
    -- Assume that $4$ does not divide $n$
    have h3 : ¬4 ∣ n := h2
    have h4 : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      omega
    rcases h4 with (h | h | h)
    · -- Case n ≡ 1 (mod 4)
      have h5 : ∃ k, n = 4 * k + 1 := by
        refine ⟨n / 4, by omega⟩
      rcases h5 with ⟨k, hk⟩
      have h6 : (1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n : ℕ) % 5 = 0 := by
        rw [show n = 4 * k + 1 by omega]
        have h7 : ∀ k : ℕ, (1 ^ (4 * k + 1) + 2 ^ (4 * k + 1) + 3 ^ (4 * k + 1) + 4 ^ (4 * k + 1) : ℕ) % 5 = 0 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
            all_goals
              norm_num at ih ⊢
              omega
        exact h7 k
      omega
    · -- Case n ≡ 2 (mod 4)
      have h5 : ∃ k, n = 4 * k + 2 := by
        refine ⟨n / 4, by omega⟩
      rcases h5 with ⟨k, hk⟩
      have h6 : (1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n : ℕ) % 5 = 0 := by
        rw [show n = 4 * k + 2 by omega]
        have h7 : ∀ k : ℕ, (1 ^ (4 * k + 2) + 2 ^ (4 * k + 2) + 3 ^ (4 * k + 2) + 4 ^ (4 * k + 2) : ℕ) % 5 = 0 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
            all_goals
              norm_num at ih ⊢
              omega
        exact h7 k
      omega
    · -- Case n ≡ 3 (mod 4)
      have h5 : ∃ k, n = 4 * k + 3 := by
        refine ⟨n / 4, by omega⟩
      rcases h5 with ⟨k, hk⟩
      have h6 : (1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n : ℕ) % 5 = 0 := by
        rw [show n = 4 * k + 3 by omega]
        have h7 : ∀ k : ℕ, (1 ^ (4 * k + 3) + 2 ^ (4 * k + 3) + 3 ^ (4 * k + 3) + 4 ^ (4 * k + 3) : ℕ) % 5 = 0 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
            all_goals
              norm_num at ih ⊢
              omega
        exact h7 k
      omega