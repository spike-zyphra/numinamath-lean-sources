import Mathlib

theorem algebra_188431 {x y : ℕ} (h1 : 2^x * 3^y = 6) (h2 : 3^x * 4^y = 12) :
    x = 1 ∧ y = 1 := by
  have h3 : x ≤ 3 := by
    by_contra h
    push_neg at h
    have h4 : x ≥ 4 := by linarith
    have h5 : 2 ^ x ≥ 16 := by
      have h6 : x ≥ 4 := h4
      have h7 : 2 ^ x ≥ 2 ^ 4 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals linarith
      have h8 : 2 ^ 4 = 16 := by norm_num
      linarith [h7, h8]
    have h8 : 3 ^ y ≥ 1 := by
      have h9 : y ≥ 0 := by linarith
      have h10 : 3 ^ y ≥ 3 ^ 0 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals linarith
      have h11 : 3 ^ 0 = 1 := by norm_num
      linarith [h10, h11]
    have h10 : 2 ^ x * 3 ^ y ≥ 16 := by
      nlinarith [h5, h8, show 2 ^ x ≥ 16 by linarith, show 3 ^ y ≥ 1 by linarith]
    nlinarith [h1, h10]
  have h4 : y ≤ 2 := by
    by_contra h
    push_neg at h
    have h5 : y ≥ 3 := by linarith
    have h6 : 3 ^ y ≥ 27 := by
      have h7 : y ≥ 3 := h5
      have h8 : 3 ^ y ≥ 3 ^ 3 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals linarith
      have h9 : 3 ^ 3 = 27 := by norm_num
      linarith [h8, h9]
    have h7 : 2 ^ x ≥ 1 := by
      have h8 : x ≥ 0 := by linarith
      have h9 : 2 ^ x ≥ 2 ^ 0 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals linarith
      have h10 : 2 ^ 0 = 1 := by norm_num
      linarith [h9, h10]
    nlinarith [h1, h6, h7]
  interval_cases x <;> interval_cases y <;> omega