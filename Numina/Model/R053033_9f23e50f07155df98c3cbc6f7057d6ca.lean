import Mathlib

theorem algebra_20975 (x : ℕ) : 6^(x + 1) - 6^x = 1080 ↔ x = 3 := by
  constructor
  · -- Forward direction: equation to x = 3
    intro h
    have eq1 : 6 ^ (x + 1) = 6 ^ x * 6 := by ring
    rw [eq1] at h
    have eq2 : (6 ^ x * 6) - 6 ^ x = 6 ^ x * 5 := by
      omega
      -- This is simple algebra: 6^(x) * 6 - 6^(x) = 6^(x) * (6 - 1) = 6^(x) * 5
    rw [eq2] at h
    have h3 : 6 ^ x = 216 := by
      omega
    have h4 : x ≤ 3 := by
      by_contra h4
      push_neg at h4
      have h5 : x ≥ 4 := by omega
      have h6 : 6 ^ x ≥ 6 ^ 4 := by
        apply Nat.pow_le_pow_of_le_right (by norm_num) h5
      norm_num at h6 h3
      linarith
    have h5 : x ≥ 3 := by
      by_contra h5
      push_neg at h5
      have h6 : x ≤ 2 := by omega
      have h7 : 6 ^ x ≤ 6 ^ 2 := by
        apply Nat.pow_le_pow_of_le_right (by norm_num) h6
      norm_num at h7 h3
      all_goals linarith
    omega
  · -- Backward direction: x = 3 to equation
    intro h
    rw [h]
    all_goals norm_num