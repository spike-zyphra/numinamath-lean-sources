import Mathlib

theorem algebra_192948 (a p : ℕ) (h₀ : 12345 * 6789 = a * 10 ^ p) (h₁ : 0 < p)
    (h₂ : 1 ≤ a ∧ a < 10) : p = 7 := by
  have h3 : a * 10 ^ p = 83810205 := by
    norm_num at h₀ ⊢
    linarith
  have h4 : p ≤ 7 := by
    by_contra h
    push_neg at h
    have h5 : p ≥ 8 := by
      omega
    have h6 : a * 10 ^ p ≥ a * 10 ^ 8 := by
      have h7 : 10 ^ p ≥ 10 ^ 8 := by
        have h8 : p ≥ 8 := by
          omega
        have h9 : 10 ^ p ≥ 10 ^ 8 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals
            omega
        linarith
      nlinarith
    have h7 : a * 10 ^ 8 ≤ 83810205 := by
      nlinarith [h3, h6]
    have h8 : a ≥ 1 := by
      linarith [h₂.1]
    have h9 : 10 ^ 8 ≤ (83810205 : ℕ) := by
      nlinarith [h7, h8]
    norm_num at h9
  have h5 : p ≥ 7 := by
    by_contra h
    push_neg at h
    have h6 : p ≤ 6 := by
      omega
    have h7 : p ≤ 6 := h6
    have h8 : a * 10 ^ p ≤ 9 * 10 ^ 6 := by
      have h9 : a ≤ 9 := by
        linarith [h₂.2]
      have h10 : 10 ^ p ≤ 10 ^ 6 := by
        have h11 : p ≤ 6 := by
          omega
        have h12 : 10 ^ p ≤ 10 ^ 6 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals
            omega
        linarith
      nlinarith [h9, h10]
    nlinarith [h3, h8]
  have hp : p = 7 := by
    omega
  exact hp