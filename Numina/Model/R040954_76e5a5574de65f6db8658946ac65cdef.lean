import Mathlib

theorem number_theory_63176 :
  ∃ a b : ℕ, a > b ∧ b > 1 ∧ ∀ k > 0, ∃ n > 0, ∃ x > 0, a * n + b = x ^ k := by
  use 6, 3
  constructor
  · -- Show that 6 > 3
    norm_num
  constructor
  · -- Show that 3 > 1
    norm_num
  · -- Show that for all positive natural numbers k, there exists a positive natural n and a positive natural x such that 6 * n + 3 = x ^ k
    intro k hk
    have h1 : k > 0 := hk
    by_cases hk2 : k > 1
    · -- k > 1
      have hk3 : k ≥ 2 := by omega
      use (3 ^ k - 3) / 6
      have h2 : (3 ^ k - 3) / 6 > 0 := by
        have h3 : 3 ^ k ≥ 9 := by
          have h4 : k ≥ 2 := hk3
          have : 3 ^ k ≥ 3 ^ (2 : ℕ) := by
            apply Nat.pow_le_pow_of_le_right
            all_goals omega
          have h5 : 3 ^ (2 : ℕ) = 9 := by norm_num
          nlinarith
        omega
      constructor
      · -- Show n > 0
        omega
      · -- Show that ∃ x > 0, 6 * n + 3 = x ^ k
        use 3
        constructor
        · -- Show that 3 > 0
          norm_num
        · -- Show that 6 * ((3 ^ k - 3) / 6) + 3 = 3 ^ k
          have h4 : (3 ^ k : ℕ) % 6 = 3 := by
            have h4 : ∀ m : ℕ, (3 ^ (m + 2) : ℕ) % 6 = 3 := by
              intro m
              induction m with
              | zero =>
                norm_num
              | succ m ih =>
                simp [Nat.pow_add, Nat.mul_mod] at ih ⊢
                all_goals omega
            have h5 : k ≥ 2 := by omega
            have h6 : ∃ m, k = m + 2 := by
              refine' ⟨k - 2, by omega⟩
            rcases h6 with ⟨m, hm⟩
            rw [hm]
            apply h4 m
          have h5 : 3 ^ k ≥ 3 := by
            have h6 : k ≥ 1 := by omega
            have h7 : 3 ^ k ≥ 3 ^ (1 : ℕ) := by
              apply Nat.pow_le_pow_of_le_right
              all_goals omega
            have h8 : 3 ^ (1 : ℕ) = 3 := by norm_num
            linarith
          have h6 : 6 * ((3 ^ k - 3) / 6) + 3 = 3 ^ k := by
            omega
          linarith
    · -- k ≤ 1
      have hk3 : k = 1 := by omega
      rw [hk3]
      use 1
      constructor
      · -- Show n > 0
        norm_num
      · -- Show that ∃ x > 0, 6 * n + 3 = x ^ 1
        use 9
        constructor
        · -- Show x > 0
          norm_num
        · -- Show 6 * 1 + 3 = 9 ^ 1
          norm_num