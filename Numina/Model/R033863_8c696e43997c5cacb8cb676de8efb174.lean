import Mathlib

theorem number_theory_210297 (n : ℕ) :
    3 ∣ n * 2 ^ n + 1 ↔ ∃ k, n = 6 * k + 1 ∨ n = 6 * k + 2 := by
  constructor
  · -- Forward direction: if $3 \mid n \cdot 2^n + 1$, then there exists a k such that n = 6k + 1 ∨ n = 6k + 2.
    intro h
    have h1 : n % 6 = 1 ∨ n % 6 = 2 := by
      have h2 : (n * 2 ^ n + 1) % 3 = 0 := by
        omega
      by_contra h1
      push_neg at h1
      have h3 : n % 6 = 0 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
        omega
      rcases h3 with (h3 | h3 | h3 | h3)
      · -- n % 6 = 0
        have h4 : n % 3 = 0 := by
          omega
        have h5 : n % 2 = 0 := by 
          omega
        have h6 : (2 ^ n) % 3 = 1 := by
          have h7 : n % 2 = 0 := h5
          have h8 : ∀ (k : ℕ), (2 ^ (2 * k)) % 3 = 1 := by
            intro k 
            induction k with 
            | zero =>
              simp 
            | succ k ih =>
              simp [pow_succ, pow_mul] at ih ⊢
              all_goals omega 
          have h9 : ∃ k : ℕ, n = 2 * k := by 
            refine' ⟨n / 2, by omega⟩ 
          rcases h9 with ⟨k, hk⟩
          rw [show n = 2 * k by linarith] 
          specialize h8 k 
          simpa using h8
        have h7 : (n * 2 ^ n) % 3 = 0 := by
          simp [Nat.mul_mod, h4, h6]
          all_goals omega 
        have h8 : (n * 2 ^ n + 1) % 3 = 1 := by
          omega
        omega
      · -- n % 6 = 3
        have h4 : n % 3 = 0 := by
          omega
        have h5 : n % 2 = 1 := by 
          omega
        have h6 : (2 ^ n) % 3 = 2 := by
          have h7 : n % 2 = 1 := h5
          have h8 : ∀ (k : ℕ), (2 ^ (2 * k + 1)) % 3 = 2 := by
            intro k 
            induction k with 
            | zero =>
              simp 
            | succ k ih =>
              simp [pow_succ, pow_mul] at ih ⊢
              all_goals omega 
          have h9 : ∃ k : ℕ, n = 2 * k + 1 := by 
            refine' ⟨(n - 1) / 2, by omega⟩ 
          rcases h9 with ⟨k, hk⟩
          rw [show n = 2 * k + 1 by linarith] 
          specialize h8 k 
          simpa using h8
        have h7 : (n * 2 ^ n) % 3 = 0 := by
          simp [Nat.mul_mod, h4, h6]
          all_goals omega 
        have h8 : (n * 2 ^ n + 1) % 3 = 1 := by
          omega 
        omega
      · -- n % 6 = 4
        have h4 : n % 3 = 1 := by
          omega
        have h5 : n % 2 = 0 := by 
          omega
        have h6 : (2 ^ n) % 3 = 1 := by
          have h7 : n % 2 = 0 := h5
          have h8 : ∀ (k : ℕ), (2 ^ (2 * k)) % 3 = 1 := by
            intro k 
            induction k with 
            | zero =>
              simp 
            | succ k ih =>
              simp [pow_succ, pow_mul] at ih ⊢
              all_goals omega 
          have h9 : ∃ k : ℕ, n = 2 * k := by 
            refine' ⟨n / 2, by omega⟩ 
          rcases h9 with ⟨k, hk⟩
          rw [show n = 2 * k by linarith] 
          specialize h8 k 
          simpa using h8
        have h7 : (n * 2 ^ n) % 3 = 1 := by
          simp [Nat.mul_mod, h4, h6]
          all_goals omega 
        have h8 : (n * 2 ^ n + 1) % 3 = 2 := by
          omega
        omega
      · -- n % 6 = 5
        have h4 : n % 3 = 2 := by
          omega
        have h5 : n % 2 = 1 := by 
          omega
        have h6 : (2 ^ n) % 3 = 2 := by
          have h7 : n % 2 = 1 := h5
          have h8 : ∀ (k : ℕ), (2 ^ (2 * k + 1)) % 3 = 2 := by
            intro k 
            induction k with 
            | zero =>
              simp 
            | succ k ih =>
              simp [pow_succ, pow_mul] at ih ⊢
              all_goals omega 
          have h9 : ∃ k : ℕ, n = 2 * k + 1 := by 
            refine' ⟨(n - 1) / 2, by omega⟩ 
          rcases h9 with ⟨k, hk⟩
          rw [show n = 2 * k + 1 by linarith] 
          specialize h8 k 
          simpa using h8
        have h7 : (n * 2 ^ n) % 3 = 1 := by
          simp [Nat.mul_mod, h4, h6]
          all_goals omega 
        have h8 : (n * 2 ^ n + 1) % 3 = 2 := by
          omega 
        omega
    have h2 : ∃ k, n = 6 * k + 1 ∨ n = 6 * k + 2 := by 
      rcases h1 with (h1 | h1)
      · -- n % 6 = 1
        refine ⟨n / 6, by omega⟩
      · -- n % 6 = 2
        refine ⟨n / 6, by omega⟩
    exact h2
  · -- Backward direction: if ∃ k, n = 6 * k + 1 ∨ n = 6 * k + 2, then 3 ∣ n * 2 ^ n + 1.
    rintro ⟨k, hk⟩
    rcases hk with (hk | hk)
    · -- n = 6k + 1
      have h1 : n % 6 = 1 := by
        omega
      have h2 : (n * 2 ^ n + 1) % 3 = 0 := by
        have h3 : n % 6 = 1 := h1
        have h4 : n % 2 = 1 := by 
          omega
        have h5 : n % 3 = 1 := by 
          omega
        have h6 : (2 ^ n) % 3 = 2 := by
          have h7 : n % 2 = 1 := h4
          have h8 : ∀ (k : ℕ), (2 ^ (2 * k + 1)) % 3 = 2 := by
            intro k 
            induction k with 
            | zero =>
              simp 
            | succ k ih =>
              simp [pow_succ, pow_mul] at ih ⊢
              all_goals omega 
          have h9 : ∃ k : ℕ, n = 2 * k + 1 := by 
            refine' ⟨(n - 1) / 2, by omega⟩ 
          rcases h9 with ⟨k, hk⟩
          rw [show n = 2 * k + 1 by linarith] 
          specialize h8 k 
          simpa using h8
        have h7 : (n * 2 ^ n) % 3 = 2 := by
          simp [Nat.mul_mod, h5, h6]
          all_goals omega 
        omega
      omega
    · -- n = 6k + 2
      have h1 : n % 6 = 2 := by
        omega
      have h2 : (n * 2 ^ n + 1) % 3 = 0 := by
        have h3 : n % 6 = 2 := h1
        have h4 : n % 2 = 0 := by 
          omega
        have h5 : n % 3 = 2 := by 
          omega
        have h6 : (2 ^ n) % 3 = 1 := by
          have h7 : n % 2 = 0 := h4
          have h8 : ∀ (k : ℕ), (2 ^ (2 * k)) % 3 = 1 := by
            intro k 
            induction k with 
            | zero =>
              simp 
            | succ k ih =>
              simp [pow_succ, pow_mul] at ih ⊢
              all_goals omega 
          have h9 : ∃ k : ℕ, n = 2 * k := by 
            refine' ⟨n / 2, by omega⟩ 
          rcases h9 with ⟨k, hk⟩
          rw [show n = 2 * k by linarith] 
          specialize h8 k 
          simpa using h8
        have h7 : (n * 2 ^ n) % 3 = 2 := by
          simp [Nat.mul_mod, h5, h6]
          all_goals omega 
        omega
      omega