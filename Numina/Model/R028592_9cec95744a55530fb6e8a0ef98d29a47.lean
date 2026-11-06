import Mathlib

theorem number_theory_225587 :
    {n : ℕ | 100 ∣ 5^n + 12 * n^2 + 12 * n + 3} = 
    {n | ∃ k : ℕ, n = 5 * k + 2} := by 
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume that 100 ∣ 5^n +12 * n^2 + 12 * n + 3, prove that ∃ k, n =5 *k +2
    intro h
    have h1 : (5 ^ n + 12 * n ^2 + 12 * n + 3) % 100 = 0 := by 
      omega
    have h25 : (5 ^ n + 12 * n ^2 + 12 * n + 3) % 25 = 0 := by 
      omega
    have h5 : n % 5 = 2 := by
      by_cases h' : n < 2
      · 
        interval_cases n <;> norm_num at h1 h25 <;> omega
      · 
        have h'' : n ≥ 2 := by omega
        have h6 : (5 ^ n) % 25 = 0 := by
          have h7 : ∀ k : ℕ, (5 ^ (k + 2)) % 25 = 0 := by
            intro k
            induction k with
            | zero =>
              norm_num
            | succ k ih =>
              simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
              all_goals omega
          specialize h7 (n - 2)
          have : n - 2 + 2 = n := by omega
          rw [this] at h7
          exact h7
        have h7 : (12 * n ^2 + 12 * n + 3) % 25 = 0 := by
          omega
        by_contra h
        push_neg at h
        have h8 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 3 ∨ n % 5 = 4 := by 
          omega
        rcases h8 with (h8 | h8 | h8 | h8)
        · -- case n ≡ 0 [5]
          have h9 : n % 5 = 0 := h8
          have h10 : n % 25 = 0 ∨ n % 25 = 5 ∨ n % 25 = 10 ∨ n % 25 = 15 ∨ n % 25 = 20 := by 
            omega
          rcases h10 with (h10 | h10 | h10 | h10 | h10) <;> 
            simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h10, h9] at h7
        · -- case n ≡ 1 [5]
          have h9 : n % 5 = 1 := h8
          have h10 : n % 25 = 1 ∨ n % 25 = 6 ∨ n % 25 = 11 ∨ n % 25 = 16 ∨ n % 25 = 21 := by 
            omega
          rcases h10 with (h10 | h10 | h10 | h10 | h10) <;> 
            simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h10, h9] at h7
        · -- case n ≡ 3 [5]
          have h9 : n % 5 = 3 := h8
          have h10 : n % 25 = 3 ∨ n % 25 = 8 ∨ n % 25 = 13 ∨ n % 25 = 18 ∨ n % 25 = 23 := by 
            omega
          rcases h10 with (h10 | h10 | h10 | h10 | h10) <;> 
            simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h10, h9] at h7
        · -- case n ≡ 4 [5]
          have h9 : n % 5 = 4 := h8
          have h10 : n % 25 = 4 ∨ n % 25 = 9 ∨ n % 25 = 14 ∨ n % 25 = 19 ∨ n % 25 = 24 := by 
            omega
          rcases h10 with (h10 | h10 | h10 | h10 | h10) <;> 
            simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h10, h9] at h7
    refine' ⟨n / 5, by omega⟩
  · -- Assume that ∃ k, n =5 *k +2, prove that 100 ∣ 5^n +12 *n^2 +12 *n +3
    rintro ⟨k, hk⟩
    rw [hk]
    have h1 : ∀ k : ℕ, (5 ^ (5 * k + 2) + 12 * (5 * k + 2) ^2 + 12 * (5 * k + 2) + 3) % 100 = 0 := by 
      intro k 
      induction k with 
      | zero => 
        norm_num 
      | succ k ih => 
        norm_num [Nat.pow_succ, Nat.mul_add, Nat.add_mul] at ih ⊢ 
        all_goals 
          omega 
    have h2 : (5 ^ (5 * k + 2) + 12 * (5 * k + 2) ^2 + 12 * (5 * k + 2) + 3) % 100 = 0 := h1 k 
    omega