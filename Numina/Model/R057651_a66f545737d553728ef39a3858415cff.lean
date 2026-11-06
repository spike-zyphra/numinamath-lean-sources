import Mathlib

theorem number_theory_204553 (n : ℕ) :
    ∃ m k, m > 0 ∧ k > 0 ∧ 2^n + 1 = m^k ∧ m ≠ 1 ∧ k ≠ 1 ↔ n = 3 := by
  use 3, 2
  constructor
  · -- Assume the left side, prove the right side
    intro h
    rcases h with ⟨h1, h2, h_eq, hne1, hne2⟩
    have h_eq2 : 2^n + 1 = 3 ^ 2 := by
      norm_num at h_eq ⊢
      all_goals linarith
    have h_eq1 : 2^n = 8 := by
      omega
    have h_eq3 : n = 3 := by
      have h1 : 2 ^ n = 8 := h_eq1
      have h3 : 2 ^ n = 2 ^ 3 := by
        rw [h1]
        all_goals norm_num
      have h4 : n = 3 := by
        exact Nat.pow_right_injective (by norm_num) h3
      exact h4
    exact h_eq3
  · -- Now reverse direction: If n = 3 then the conditions hold
    intro h_eq
    rw [h_eq]
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num