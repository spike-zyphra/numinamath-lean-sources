import Mathlib

theorem number_theory_634028 {a b c: ℕ} (h: 2 ^ a * 3 ^ b * 7 ^ c = 1176):
  2 * a + 3 * b + 7 * c = 23 := by
  have h1 : a ≤ 10 := by
    by_contra h2
    push_neg at h2
    have h3 : 2 ^ a ≥ 2 ^ 11 := by
      have : a ≥ 11 := by omega
      exact Nat.pow_le_pow_of_le_right (by norm_num) this
    have h4 : 2 ^ a * 3 ^ b * 7 ^ c ≥ 2 ^ 11 * 1 * 1 := by
      have h5 : 2 ^ a ≥ 2 ^ 11 := h3
      have h6 : 3 ^ b ≥ 1 := by
        apply Nat.one_le_pow
        all_goals norm_num
      have h7 : 7 ^ c ≥ 1 := by
        apply Nat.one_le_pow
        all_goals norm_num
      have h8 : (2 ^ a : ℕ) * (3 ^ b : ℕ) * (7 ^ c : ℕ) ≥ (2 ^ 11 : ℕ) * (1 : ℕ) * (1 : ℕ) := by
        have h9 : (2 ^ a : ℕ) ≥ (2 ^ 11 : ℕ) := h3
        have h10 : (3 ^ b : ℕ) ≥ (1 : ℕ) := h6
        have h11 : (7 ^ c : ℕ) ≥ (1 : ℕ) := h7
        have h12 : (2 ^ a : ℕ) * (3 ^ b : ℕ) ≥ (2 ^ 11 : ℕ) * (1 : ℕ) := by
          nlinarith [h9, h10]
        have h13 : (2 ^ a : ℕ) * (3 ^ b : ℕ) * (7 ^ c : ℕ) ≥ (2 ^ 11 : ℕ) * (1 : ℕ) * (1 : ℕ) := by
          nlinarith [h12, h7]
        linarith
      omega
    have h5 : 2 ^ 11 * 1 * 1 > 1176 := by
      norm_num
    have h5' : 2 ^ a * 3 ^ b * 7 ^ c > 1176 := by
      linarith [h4, h5]
    linarith [h, h5']
  have h2 : b ≤ 10 := by
    by_contra h3
    push_neg at h3
    have h4 : 3 ^ b ≥ 3 ^ 11 := by
      have : b ≥ 11 := by omega
      exact Nat.pow_le_pow_of_le_right (by norm_num) this
    have h5 : 2 ^ a * 3 ^ b * 7 ^ c ≥ 1 * 3 ^ 11 * 1 := by
      have h6 : 2 ^ a ≥ 1 := by
        apply Nat.one_le_pow
        all_goals norm_num
      have h7 : 3 ^ b ≥ 3 ^ 11 := h4
      have h8 : 7 ^ c ≥ 1 := by
        apply Nat.one_le_pow
        all_goals norm_num
      have h9 : (2 ^ a : ℕ) * (3 ^ b : ℕ) * (7 ^ c : ℕ) ≥ (1 : ℕ) * (3 ^ 11 : ℕ) * (1 : ℕ) := by
        have h10 : (3 ^ b : ℕ) ≥ (3 ^ 11 : ℕ) := h4
        have h11 : (2 ^ a : ℕ) ≥ (1 : ℕ) := h6
        have h12 : (7 ^ c : ℕ) ≥ (1 : ℕ) := h8
        have h13 : (2 ^ a : ℕ) * (3 ^ b : ℕ) ≥ (1 : ℕ) * (3 ^ 11 : ℕ) := by
          nlinarith [h11, h10]
        have h14 : (2 ^ a : ℕ) * (3 ^ b : ℕ) * (7 ^ c : ℕ) ≥ (1 : ℕ) * (3 ^ 11 : ℕ) * (1 : ℕ) := by
          nlinarith [h13, h12]
        linarith
      omega
    have h5' : 1 * 3 ^ 11 * 1 > 1176 := by
      norm_num
    have h6 : 2 ^ a * 3 ^ b * 7 ^ c > 1176 := by
      linarith [h5, h5']
    linarith [h, h6]
  have h3 : c ≤ 10 := by
    by_contra h4
    push_neg at h4
    have h5 : 7 ^ c ≥ 7 ^ 11 := by
      have : c ≥ 11 := by omega
      exact Nat.pow_le_pow_of_le_right (by norm_num) this
    have h6 : 2 ^ a * 3 ^ b * 7 ^ c ≥ 1 * 1 * 7 ^ 11 := by
      have h7 : 2 ^ a ≥ 1 := by
        apply Nat.one_le_pow
        all_goals norm_num
      have h8 : 3 ^ b ≥ 1 := by
        apply Nat.one_le_pow
        all_goals norm_num
      have h9 : 7 ^ c ≥ 7 ^ 11 := h5
      have h10 : (2 ^ a : ℕ) * (3 ^ b : ℕ) * (7 ^ c : ℕ) ≥ (1 : ℕ) * (1 : ℕ) * (7 ^ 11 : ℕ) := by
        have h11 : (2 ^ a : ℕ) ≥ (1 : ℕ) := h7
        have h12 : (3 ^ b : ℕ) ≥ (1 : ℕ) := h8
        have h13 : (7 ^ c : ℕ) ≥ (7 ^ 11 : ℕ) := h9
        have h14 : (2 ^ a : ℕ) * (3 ^ b : ℕ) ≥ (1 : ℕ) * (1 : ℕ) := by
          nlinarith [h11, h12]
        have h15 : (2 ^ a : ℕ) * (3 ^ b : ℕ) * (7 ^ c : ℕ) ≥ (1 : ℕ) * (1 : ℕ) * (7 ^ 11 : ℕ) := by
          nlinarith [h14, h13]
        linarith
      omega
    have h5' : 1 * 1 * 7 ^ 11 > 1176 := by
      norm_num
    have h6 : 2 ^ a * 3 ^ b * 7 ^ c > 1176 := by
      linarith [h6, h5']
    linarith [h, h6]
  interval_cases a <;> interval_cases b <;> interval_cases c
  <;> omega