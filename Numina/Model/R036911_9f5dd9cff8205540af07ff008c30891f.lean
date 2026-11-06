import Mathlib

theorem number_theory_112304 (n : ℕ) : 3 ∣ (2^n + 1) ↔ Odd n := by
  constructor
  · -- Assume 3 divides (2^n + 1), show n is odd
    intro h
    by_cases h3 : n % 2 = 0
    · -- Assume n is even
      -- Then n is even, so n=2k
      have h4 : ∃ k, n = 2 * k := by
        refine' ⟨n / 2, by omega⟩
      rcases h4 with ⟨k, hk⟩
      have h5 : (2 : ℕ) ^ n = ((2 : ℕ) ^ k) ^ 2 := by
        calc
          (2 : ℕ) ^ n = (2 : ℕ) ^ (2 * k) := by rw [hk]
          _ = ((2 : ℕ) ^ k) ^ 2 := by ring_nf
      have h6 : ((2 : ℕ) ^ n) % 3 = 1 := by
        have h7 : ((2 : ℕ) ^ k) % 3 = 1 ∨ ((2 : ℕ) ^ k) % 3 = 2 := by
          have h8 : ∀ (m : ℕ), (2 : ℕ) ^ m % 3 = 1 ∨ (2 : ℕ) ^ m % 3 = 2 := by
            intro m 
            induction m with
            | zero =>
              simp 
            | succ m ih =>
              simp [pow_succ, Nat.mul_mod] at ih ⊢
              omega 
          specialize h8 k 
          simpa using h8 
        rcases h7 with (h7 | h7)
        · 
          simp [h5, Nat.pow_mod, h7] 
        · 
          simp [h5, Nat.pow_mod, h7] 
      omega 
    · -- n is odd
      have h3' : n % 2 = 1 := by omega 
      have : Odd n := by 
        exact ⟨n / 2, by omega⟩ 
      tauto 
  · -- Assume n is odd, show 3 divides (2^n + 1)
    intro h 
    have h3 : n % 2 = 1 := by 
      obtain ⟨k, hk⟩ := h 
      omega 
    have h4 : ∃ k, n = 2 * k + 1 := by 
      refine' ⟨(n - 1) / 2, by omega⟩ 
    rcases h4 with ⟨k, hk⟩ 
    have h5 : (2 : ℕ) ^ n % 3 = 2 := by 
      rw [show (2 : ℕ) ^ n = (2 : ℕ) ^ (2 * k + 1) by rw [hk] ]
      have h6 : (2 : ℕ) ^ (2 * k + 1) % 3 = 2 := by 
        have h7 : ∀ (m : ℕ), (2 : ℕ) ^ (2 * m + 1) % 3 = 2 := by 
          intro m 
          induction m with 
          | zero =>
            norm_num 
          | succ m ih =>
            simp [pow_succ, pow_mul, Nat.pow_mod] at ih ⊢ 
            omega 
        specialize h7 k 
        simpa using h7 
      omega 
    omega