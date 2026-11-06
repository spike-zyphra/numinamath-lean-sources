import Mathlib

theorem number_theory_204782 :
    {n : ℕ | 0 < n ∧ 7 ∣ (2 ^ n - 1)} = {n : ℕ | ∃ k, 0 < k ∧ n = 3 * k} ∧
    ∀ n : ℕ, 0 < n → ¬7 ∣ (2 ^ n + 1) := by

  constructor
  · -- First part equality of sets
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
    constructor
    · -- First direction: if $n$ is positive and $7 \div 2^n-1$ then $n = 3k$
      intro h
      rcases h with ⟨hpos, hdiv⟩
      have h1 : n % 3 = 1 ∨ n % 3 = 2 ∨ n % 3 = 0 := by 
        omega
      rcases h1 with (h1 | h1 | h1)
      · -- n ≡ 1 [MOD 3]
        have h2 : (2 ^ n) % 7 = 2 := by
          have h3 : ∀ m : ℕ, (2 ^ (3 * m + 1)) % 7 = 2 := by 
            intro m 
            induction m with 
            | zero => norm_num 
            | succ m ih => 
              simp [Nat.pow_add, Nat.pow_mul] at ih ⊢ 
              omega 
          have h4 : n = 3 * (n / 3) + 1 := by 
            omega 
          rw [h4]
          apply h3 (n / 3)
        have h4 : ¬ (7 ∣ (2 ^ n - 1)) := by
          have h5 : (2 ^ n) % 7 = 2 := h2
          have h6 : n ≥ 1 := by 
            omega 
          have h7 : (2 ^ n - 1) % 7 = 1 := by 
            have h5' : (2 ^ n) % 7 = 2 := h2
            have h8 : n ≥ 1 := by 
              omega 
            have h4 : (2 ^ n) ≥ 2 := by
              have : n ≥ 1 := by omega
              have h12 : 2 ^ n ≥ 2 ^ 1 := by 
                apply Nat.pow_le_pow_of_le_right 
                all_goals linarith 
              have h13 : 2 ^ 1 = 2 := by norm_num 
              rw [h13] at h12 
              linarith 
            omega 
          omega 
        contradiction 
      · -- n ≡ 2 [MOD 3]
        have h2 : (2 ^ n) % 7 = 4 := by
          have h3 : ∀ m : ℕ, (2 ^ (3 * m + 2)) % 7 = 4 := by 
            intro m 
            induction m with 
            | zero => norm_num 
            | succ m ih => 
              simp [Nat.pow_add, Nat.pow_mul] at ih ⊢ 
              omega 
          have h4 : n = 3 * (n / 3) + 2 := by 
            omega 
          rw [h4]
          apply h3 (n / 3)
        have h4 : ¬ (7 ∣ (2 ^ n - 1)) := by
          have h5 : (2 ^ n) % 7 = 4 := h2
          have h6 : n ≥ 1 := by 
            omega 
          have h7 : (2 ^ n - 1) % 7 = 3 := by 
            have h5' : (2 ^ n) % 7 = 4 := h2
            have h8 : n ≥ 1 := by 
              omega 
            have h4 : (2 ^ n) ≥ 2 := by
              have : n ≥ 1 := by omega
              have h12 : 2 ^ n ≥ 2 ^ 1 := by 
                apply Nat.pow_le_pow_of_le_right 
                all_goals linarith 
              have h13 : 2 ^ 1 = 2 := by norm_num 
              rw [h13] at h12 
              linarith 
            omega 
          omega 
        contradiction 
      · -- n ≡ 0 [MOD 3]
        have h2 : n % 3 = 0 := by 
          omega 
        have h3 : ∃ k, 0 < k ∧ n = 3 * k := by
          refine' ⟨n / 3, by omega, by omega⟩ 
        assumption 
    · -- Backward direction: if ∃ k, 0 < k ∧ n = 3 * k then 0 < n ∧ 7 ∣ (2 ^ n - 1)
      rintro ⟨k, hk1, hk2⟩
      have hn : 0 < n := by
        omega 
      have h1 : n = 3 * k := by 
        omega 
      have h2 : 7 ∣ (2 ^ n - 1) := by
        rw [h1]
        have h4 : ∀ (k : ℕ), 0 < k → 7 ∣ (2 ^ (3 * k) - 1) := by
          intro k hk
          induction k with 
          | zero => 
            linarith 
          | succ k ih => 
            cases k with
            | zero => 
              simp [pow_succ, pow_mul]
            | succ k => 
              simp [pow_succ, pow_mul] at ih ⊢ 
              omega 
        apply h4 k hk1 
      exact ⟨hn, h2⟩ 
  · -- ∀ n : ℕ, 0 < n → ¬7 ∣ (2 ^ n + 1)
    intro n hn
    intro h 
    have h1 : n % 3 = 1 ∨ n % 3 = 2 ∨ n % 3 = 0 := by 
      omega 
    rcases h1 with (h1 | h1 | h1)
    · -- n ≡ 1 [MOD 3]
      have h2 : (2 ^ n) % 7 = 2 := by 
        have h3 : ∀ m : ℕ, (2 ^ (3 * m + 1)) % 7 = 2 := by 
          intro m 
          induction m with 
          | zero => norm_num 
          | succ m ih => 
            simp [Nat.pow_add, Nat.pow_mul] at ih ⊢ 
            omega 
        have h4 : n = 3 * (n / 3) + 1 := by 
          omega 
        rw [h4]
        apply h3 (n / 3)
      omega
    · -- n ≡ 2 [MOD 3]
      have h2 : (2 ^ n) % 7 = 4 := by 
        have h3 : ∀ m : ℕ, (2 ^ (3 * m + 2)) % 7 = 4 := by 
          intro m 
          induction m with 
          | zero => norm_num 
          | succ m ih => 
            simp [Nat.pow_add, Nat.pow_mul] at ih ⊢ 
            omega 
        have h4 : n = 3 * (n / 3) + 2 := by 
          omega 
        rw [h4]
        apply h3 (n / 3)
      omega
    · -- n ≡ 0 [MOD 3]
      have h2 : (2 ^ n) % 7 = 1 := by 
        have h3 : ∀ m : ℕ, (2 ^ (3 * m)) % 7 = 1 := by 
          intro m 
          induction m with 
          | zero => norm_num 
          | succ m ih => 
            simp [Nat.pow_add, Nat.pow_mul] at ih ⊢ 
            omega 
        have h4 : n = 3 * (n / 3) := by 
          omega 
        rw [h4]
        apply h3 (n / 3)
      omega