import Mathlib

theorem algebra_12973 (x : ℕ) : 27 = 3 * 9 ^ (x - 1) ↔ x = 2 := by
  constructor
  · -- Assume 27 = 3 * 9 ^ (x - 1) prove x = 2
    intro h
    have h1 : x ≤ 4 := by
      by_contra h2
      push_neg at h2
      have h2' : x ≥ 5 := by omega
      have h3 : 3 * 9 ^ (x - 1) ≥ 3 * 9 ^ (5 - 1 : ℕ) := by
        have h4 : x - 1 ≥ (5 - 1 : ℕ) := by
          omega
        have h5 : 9 ^ (x - 1) ≥ 9 ^ (5 - 1 : ℕ) := by
          apply Nat.pow_le_pow_of_le_right
          all_goals
            norm_num
          all_goals
            omega
        have h6 : 3 * 9 ^ (x - 1) ≥ 3 * 9 ^ (5 - 1 : ℕ) := by
          nlinarith [h5]
          <;> omega
        linarith
      have h7 : 3 * 9 ^ (5 - 1 : ℕ) ≥ 2187 := by
        norm_num
      have h8 : 3 * 9 ^ (x - 1) ≥ 2187 := by
        linarith [h3, h7]
      linarith [h, h8]
    interval_cases x <;> norm_num at h ⊢ <;> all_goals omega
  · -- Assume x = 2 prove 27 = 3 * 9 ^ (x - 1)
    intro h
    rw [h]
    all_goals norm_num
    all_goals omega