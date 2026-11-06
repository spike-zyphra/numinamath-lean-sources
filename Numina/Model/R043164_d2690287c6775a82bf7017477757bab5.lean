import Mathlib

theorem algebra_20605 (x : ℕ) (hx : x > 0) (h : 1^x + 2^x + 5^x = 642) : x = 4 := by
  have h1 : x ≤ 5 := by
    by_contra h2
    push_neg at h2
    have h2' : x ≥ 6 := by omega
    have h3 : (1 : ℕ) ^ x + (2 : ℕ) ^ x + (5 : ℕ) ^ x ≥ (1 : ℕ) ^ 6 + (2 : ℕ) ^ 6 + (5 : ℕ) ^ 6 := by
      have h4 : (1 : ℕ) ^ x ≥ (1 : ℕ) ^ 6 := by
        have h5 : x ≥ 6 := h2'
        exact Nat.pow_le_pow_of_le_right (by norm_num) h5
      have h6 : (2 : ℕ) ^ x ≥ (2 : ℕ) ^ 6 := by
        have h7 : x ≥ 6 := h2'
        exact Nat.pow_le_pow_of_le_right (by norm_num) h7
      have h7 : (5 : ℕ) ^ x ≥ (5 : ℕ) ^ 6 := by
        have h8 : x ≥ 6 := h2'
        exact Nat.pow_le_pow_of_le_right (by norm_num) h8
      linarith
    have h4 : (1 : ℕ) ^ x + (2 : ℕ) ^ x + (5 : ℕ) ^ x = 642 := by linarith
    norm_num at h3 h4
    all_goals linarith
  interval_cases x <;> norm_num at h <;> omega