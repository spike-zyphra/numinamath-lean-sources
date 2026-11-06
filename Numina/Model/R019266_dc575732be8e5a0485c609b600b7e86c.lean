import Mathlib

theorem algebra_19518 (n : ℕ) : (9 ^ n * 3 ^ (2 * n + 1)) / 81 = 243 ↔ n = 2 := by
  constructor
  · -- Forward implication: if (9^n * 3^(2*n+1)) / 81 = 243, then n = 2
    intro h
    have h1 : n = 2 := by
      by_cases h2 : n ≤ 5
      ·
        interval_cases n <;> norm_num at h ⊢ <;> omega
      · -- n > 5
        push_neg at h2
        have h2' : n > 2 := by omega
        have h3 : (9 ^ n * 3 ^ (2 * n + 1)) / 81 > 243 := by
          have h4 : n ≥ 3 := by omega
          have h5 : 9 ^ n * 3 ^ (2 * n + 1) ≥ 9 ^ 3 * 3 ^ (2 * 3 + 1) := by
            have h5a : n ≥ 3 := by omega
            have h5b : 9 ^ n ≥ 9 ^ 3 := by
              apply Nat.pow_le_pow_of_le_right
              norm_num
              all_goals omega
            have h6a : 2 * n + 1 ≥ 2 * 3 + 1 := by omega
            have h6b : 3 ^ (2 * n + 1) ≥ 3 ^ (2 * 3 + 1) := by
              apply Nat.pow_le_pow_of_le_right
              norm_num
              all_goals omega
            have h5c : 9 ^ n * 3 ^ (2 * n + 1) ≥ 9 ^ 3 * 3 ^ (2 * 3 + 1) := by
              nlinarith [h5b, h6b, mul_pos (show 0 < 9 ^ 3 by positivity) (show 0 < 3 ^ (2 * 3 + 1) by positivity)]
            linarith
          have h6 : (9 ^ n * 3 ^ (2 * n + 1)) / 81 ≥ (9 ^ 3 * 3 ^ (2 * 3 + 1)) / 81 := by
            apply Nat.div_le_div_right
            all_goals linarith
          have h7 : (9 ^ 3 * 3 ^ (2 * 3 + 1)) / 81 > 243 := by
            norm_num
          have h8 : (9 ^ n * 3 ^ (2 * n + 1)) / 81 ≥ (9 ^ 3 * 3 ^ (2 * 3 + 1)) / 81 := by
            apply Nat.div_le_div_right
            all_goals linarith
          omega
        omega
    exact h1
  · -- Backward implication: if n = 2, then (9^n * 3^(2*n+1)) / 81 = 243
    intro h
    rw [h]
    all_goals norm_num