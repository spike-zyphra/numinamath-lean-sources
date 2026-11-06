import Mathlib

theorem number_theory_279961 (n : ℕ) (hn : n > 0) :
    ∃ a b, (10 ^ n) = a ^ 2 + b ^ 2 := by 
  by_cases h : n % 2 = 1
  · -- n is odd
    have h1 : ∀ k : ℕ, ∃ a b, (10 ^ (2 * k + 1) ) = a ^ 2 + b ^ 2 := by
      intro k 
      induction k with 
      | zero =>
        use 3, 1 
        norm_num 
      | succ k ih => 
        rcases ih with ⟨a, b, h_eq⟩
        use 10 * a, 10 * b
        norm_num [Nat.pow_succ, Nat.pow_mul] at h_eq ⊢
        nlinarith [h_eq]
    have h2 := h1 ((n - 1) / 2)
    rcases h2 with ⟨a, b, h_eq⟩
    have h3 : 2 * ((n - 1) / 2) + 1 = n := by 
      omega
    rw [h3] at h_eq
    exact ⟨a, b, h_eq⟩
  · -- n is even
    have h2 : n % 2 = 0 := by 
      omega
    have h1 : ∀ k : ℕ, ∃ a b, (10 ^ (2 * k) ) = a ^ 2 + b ^ 2 := by 
      intro k 
      use 10 ^ k, 0 
      ring
    have h4 : ∃ a b, (10 ^ n ) = a ^ 2 + b ^ 2 := by
      have h3 : n % 2 = 0 := h2 
      have h5 : ∃ k : ℕ, n = 2 * k := by 
        refine' ⟨n / 2, by omega⟩
      rcases h5 with ⟨k, hk⟩
      have h2 := h1 k 
      rw [show n = 2 * k by omega] 
      exact h2 
    simpa using h4