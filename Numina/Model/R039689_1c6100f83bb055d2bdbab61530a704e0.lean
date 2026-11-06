import Mathlib

theorem algebra_596944 (a b c d : ℕ) (h : (a + b)^2 + 3 * a + 2 * b = (c + d)^2 + 3 * c + 2 * d) :
    a = c ∧ b = d := by 
  have h1 : a + b ≤ c + d := by
    by_contra h2
    push_neg at h2
    have h3 : (a + b) ^ 2 + 3 * a + 2 * b > (c + d) ^ 2 + 3 * c + 2 * d := by
      have h4 : a + b > c + d := by
        omega
      have h5 : (a + b) ^ 2 ≥ (c + d + 1) ^ 2 := by
        have h6 : a + b ≥ c + d + 1 := by
          omega
        have h7 : (a + b) ^ 2 ≥ (c + d + 1) ^ 2 := by
          apply Nat.pow_le_pow_of_le_left h6 2
        linarith
      nlinarith [sq_nonneg (a - c : ℤ), sq_nonneg (b - d : ℤ)]
    nlinarith
  have h2 : c + d ≤ a + b := by
    by_contra h3
    push_neg at h3
    have h4 : (a + b) ^ 2 + 3 * a + 2 * b < (c + d) ^ 2 + 3 * c + 2 * d := by
      have h5 : c + d > a + b := by
        omega
      have h6 : (c + d) ^ 2 ≥ (a + b + 1) ^ 2 := by
        have h7 : c + d ≥ a + b + 1 := by
          omega
        have h8 : (c + d) ^ 2 ≥ (a + b + 1) ^ 2 := by
          apply Nat.pow_le_pow_of_le_left h7 2
        linarith
      nlinarith [sq_nonneg (a - c : ℤ), sq_nonneg (b - d : ℤ)]
    nlinarith
  have h3 : a + b = c + d := by
    linarith
  have h4 : (a + b) ^ 2 + 3 * a + 2 * b = (c + d) ^ 2 + 3 * c + 2 * d := h
  have h5 : (a + b) ^ 2 = (c + d) ^ 2 := by
    have h6 : a + b = c + d := h3
    have h7 : (a + b) ^ 2 = (c + d) ^ 2 := by
      rw [show (a + b) = (c + d) by omega]
    exact h7
  have h6 : 3 * a + 2 * b = 3 * c + 2 * d := by 
    nlinarith [h4, h5]
  have h7 : a = c := by 
    omega 
  have h8 : b = d := by 
    omega 
  exact ⟨h7, h8⟩