import Mathlib

theorem number_theory_164665 :
    {(m, n) : ℕ × ℕ | 0 < m ∧ 0 < n ∧ |(12 ^ m : ℤ) - 5 ^ n| = 7} = {(1, 1)} := by
  ext ⟨m, n⟩
  simp
  constructor
  · -- First, show that if ((m, n) : ℕ × ℕ) ∈ {(m, n) : ℕ × ℕ | 0 < m ∧ 0 < n ∧ |(12 ^ m : ℤ) - 5 ^ n| = 7}, then ((m, n) : ℕ × ℕ) ∈ {(1, 1)}
    rintro ⟨hm, hn, h⟩
    have h1 : m > 0 := hm
    have h2 : n > 0 := hn
    have h3 : (12 ^ m : ℤ) - 5 ^ n = 7 ∨ (12 ^ m : ℤ) - 5 ^ n = -7 := by
      cases' abs_cases ((12 ^ m : ℤ) - 5 ^ n) with h4 h4 <;> omega
    rcases h3 with h_eq | h_eq
    · -- case where $12^m - 5^n = 7$
      have h_eq1 : (12 ^ m : ℤ) = 5 ^ n + 7 := by linarith
      have h4 : m = 1 := by
        by_cases h5 : m > 1
        · -- m > 1
          have h6 : m ≥ 2 := by omega
          have h7 : (12 ^ m : ℤ) % 24 = 0 := by
            have h12 : m ≥ 2 := by omega
            have h13 : ∀ k : ℕ, (12 ^ (k + 2) : ℤ) % 24 = 0 := by
              intro k
              induction k with
              | zero =>
                norm_num
              | succ k ih =>
                simp [pow_add, pow_mul] at ih ⊢
                all_goals omega
            specialize h13 (m - 2)
            have h14 : m - 2 + 2 = m := by omega
            rw [h14] at h13
            all_goals omega
          -- analyze RHS of equation
          have h12 : (5 ^ n : ℤ) % 24 = 1 ∨ (5 ^ n : ℤ) % 24 = 5 := by
            have h9 : ∀ k : ℕ, (5 ^ (k + 1) : ℤ) % 24 = 5 ∨ (5 ^ (k + 1) : ℤ) % 24 = 1 := by
              intro k
              induction k with
              | zero =>
                norm_num
                <;> omega
              | succ k ih =>
                simp [pow_add, pow_mul] at ih ⊢
                all_goals omega
            specialize h9 (n - 1)
            have h10 : n - 1 + 1 = n := by omega
            rw [h10] at h9
            all_goals omega
          omega
        · -- m ≤ 1, so m = 1
          omega
      -- m = 1
      rw [h4] at h_eq1
      have h6 : (5 ^ n : ℤ) = 5 := by
        norm_num at h_eq1
        nlinarith
      have h7 : n = 1 := by
        have h8 : 5 ^ n = 5 ^ 1 := by
          have h9 : (5 ^ n : ℤ) = (5 : ℤ) := by
            nlinarith
          norm_cast at h9 ⊢
          all_goals linarith
        have h11 : n = 1 := by
          exact Nat.pow_right_injective (by norm_num) h8
        exact h11
      simp [h4, h7]
    · -- case where $5^n - 12^m = 7$
      have h_eq1 : (5 ^ n : ℤ) = 12 ^ m + 7 := by linarith
      have h6 : (12 ^ m : ℤ) % 4 = 0 := by
        have h7 : ∀ k : ℕ, (12 ^ (k + 1) : ℤ) % 4 = 0 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [pow_add, pow_mul] at ih ⊢
            all_goals omega
        specialize h7 (m - 1)
        have h8 : m - 1 + 1 = m := by omega
        rw [h8] at h7
        all_goals omega
      have h7 : (5 ^ n : ℤ) % 4 = 1 := by
        have h8 : ∀ k : ℕ, (5 ^ (k + 1) : ℤ) % 4 = 1 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [pow_add, pow_mul] at ih ⊢
            all_goals omega
        specialize h8 (n - 1)
        have h9 : n - 1 + 1 = n := by omega
        rw [h9] at h8
        all_goals omega
      omega
  · -- Now the reverse direction: (1, 1) is in the set
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
      all_goals norm_num [abs]
      all_goals norm_num
      all_goals norm_num [abs]