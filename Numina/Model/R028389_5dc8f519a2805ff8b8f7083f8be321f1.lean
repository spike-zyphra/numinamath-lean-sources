import Mathlib

theorem number_theory_87836 (k : ℕ) :
    ∃ n m, n > 0 ∧ m > 0 ∧ n ^ m = 3 ^ k + 5 ^ k ∧ m ≥ 2 ↔ k = 1 := by 
  use 2, 3
  constructor
  · -- (∧) → k = 1
    intro h
    rcases h with ⟨h1, h2, h3, h4⟩
    have eq1 : 3 ^ k + 5 ^ k = 8 := by
      linarith
    have h5 : k = 1 := by
      have h1 : 3 ^ k + 5 ^ k = 8 := by
        linarith
      have h2 : k ≥ 1 := by
        by_contra h
        push_neg at h
        have h3 : k = 0 := by
          omega
        rw [h3] at h1
        norm_num at h1
      by_cases h4 : k ≥ 2
      · -- k >= 2
        have h5 : 3 ^ k ≥ 9 := by
          have h6 : 3 ^ 2 = 9 := by norm_num
          have h7 : 3 ^ k ≥ 3 ^ 2 := by
            apply Nat.pow_le_pow_of_le_right
            all_goals linarith
            all_goals omega
          nlinarith [h6]
        have h8 : 5 ^ k ≥ 25 := by
          have h9 : 5 ^ 2 = 25 := by norm_num
          have h10 : 5 ^ k ≥ 5 ^ 2 := by
            apply Nat.pow_le_pow_of_le_right
            all_goals linarith
            all_goals omega
          nlinarith [h9]
        have h11 : 3 ^ k + 5 ^ k ≥ 34 := by
          linarith
        linarith
      · -- k < 2
        have hk1 : k < 2 := by omega
        have hk0 : k = 1 := by
          omega
        tauto
    tauto
  · -- k = 1 → (∧)
    intro h
    rw [h] 
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num