import Mathlib

theorem number_theory_141767 (n : ℕ) (hn : n ≠ 0) :
    3 ∣ n * 2 ^ n + 1 ↔ n % 6 = 1 ∨ n % 6 = 2 := by
  constructor
  · -- Assume 3 ∣ n * 2 ^ n + 1, prove n % 6 = 1 ∨ n % 6 = 2
    intro h
    have h1 : (n * 2 ^ n + 1) % 3 = 0 := by 
      omega
    have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases h2 with (h2 | h2)
    · -- n is even
      have h4 : (2 ^ n) % 3 = 1 := by
        have h5 : n % 2 = 0 := by 
          omega
        have h6 : ∃ k : ℕ, n = 2 * k := by
          refine' ⟨n / 2, by omega⟩
        rcases h6 with ⟨k, hk⟩
        rw [show n = 2 * k by omega]
        have h7 : ∀ k : ℕ, (2 ^ (2 * k) ) % 3 = 1 := by
          intro k
          induction k with 
          | zero =>
            norm_num
          | succ k ih =>
            simp [pow_mul, pow_add] at ih ⊢
            all_goals omega
        apply h7 k
      have h7 : n % 3 = 2 := by 
        have eq1 : (n * 2 ^ n + 1) % 3 = 0 := h1
        simp [Nat.add_mod, Nat.mul_mod, h4] at eq1 
        omega
      have h8 : n % 6 = 2 := by
        omega
      right
      omega
    · -- n is odd
      have h4 : (2 ^ n) % 3 = 2 := by
        have h5 : n % 2 = 1 := by 
          omega
        have h6 : ∃ k : ℕ, n = 2 * k + 1 := by 
          refine' ⟨(n - 1) / 2, by omega⟩ 
        rcases h6 with ⟨k, hk⟩ 
        rw [show n = 2 * k + 1 by omega] 
        have h7 : ∀ k : ℕ, (2 ^ (2 * k + 1) ) % 3 = 2 := by 
          intro k 
          induction k with 
          | zero =>
            norm_num 
          | succ k ih =>
            simp [pow_add, pow_mul] at ih ⊢ 
            all_goals omega 
        apply h7 k 
      have h7 : n % 3 = 1 := by 
        have eq1 : (n * 2 ^ n + 1) % 3 = 0 := h1
        simp [Nat.add_mod, Nat.mul_mod, h4] at eq1 
        omega
      have h8 : n % 6 = 1 := by
        omega
      left
      omega 
  · -- Assume n % 6 = 1 ∨ n % 6 = 2, prove 3 ∣ n * 2 ^ n + 1
    intro h 
    have h2 : (n * 2 ^ n + 1) % 3 = 0 := by
      rcases h with (h | h)
      · -- n % 6 = 1 
        have h1 : n % 6 = 1 := h
        have h3 : n % 2 = 1 := by 
          omega
        have h4 : n % 3 = 1 := by
          omega
        have h6 : (2 ^ n) % 3 = 2 := by 
          have h5 : n % 2 = 1 := by 
            omega
          have h6 : ∃ k : ℕ, n = 2 * k + 1 := by 
            refine' ⟨(n - 1) / 2, by omega⟩ 
          rcases h6 with ⟨k, hk⟩ 
          rw [show n = 2 * k + 1 by omega] 
          have h7 : ∀ k : ℕ, (2 ^ (2 * k + 1) ) % 3 = 2 := by 
            intro k 
            induction k with 
            | zero =>
              norm_num 
            | succ k ih =>
              simp [pow_add, pow_mul] at ih ⊢ 
              all_goals omega 
          apply h7 k
        simp [Nat.add_mod, Nat.mul_mod, h6] at *
        all_goals omega
      · -- n % 6 = 2 
        have h1 : n % 6 = 2 := h
        have h3 : n % 2 = 0 := by 
          omega
        have h4 : n % 3 = 2 := by 
          omega
        have h6 : (2 ^ n) % 3 = 1 := by
          have h5 : n % 2 = 0 := by 
            omega
          have h6 : ∃ k : ℕ, n = 2 * k := by 
            refine' ⟨n / 2, by omega⟩ 
          rcases h6 with ⟨k, hk⟩ 
          rw [show n = 2 * k by omega] 
          have h7 : ∀ k : ℕ, (2 ^ (2 * k) ) % 3 = 1 := by 
            intro k 
            induction k with 
            | zero =>
              norm_num 
            | succ k ih =>
              simp [pow_mul, pow_add] at ih ⊢ 
              all_goals omega 
          apply h7 k 
        simp [Nat.add_mod, Nat.mul_mod, h6] at *
        all_goals omega 
    omega