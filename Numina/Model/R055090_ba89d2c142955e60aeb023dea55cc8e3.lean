import Mathlib

theorem algebra_14329 (x : ℕ) : 2^x + 2^x + 2^x + 2^x = 512 ↔ x = 7 := by
  constructor
  · -- Forward direction: if 2^x + 2^x + 2^x + 2^x = 512, then x = 7
    intro h
    have h1 : 2^x + 2^x + 2^x + 2^x = 4 * 2^x := by
      omega
    rw [h1] at h
    have h2 : 2^x = 128 := by
      omega
    have h3 : x = 7 := by
      have h4 : 2^x = 128 := h2
      have h5 : x = 7 := by
        have h6 : x ≤ 7 := by
          by_contra h
          push_neg at h
          have h7 : x ≥ 8 := by
            omega
          have h8 : 2 ^ x ≥ 2 ^ 8 := by
            have h9 : x ≥ 8 := h7
            exact (Nat.pow_le_pow_of_le_right (by norm_num) h9)
          norm_num at h8
          omega  -- Contradiction with 2^x = 128
        have h7 : x ≥ 7 := by
          by_contra h
          push_neg at h
          have h8 : x ≤ 6 := by
            omega
          have h9 : 2 ^ x ≤ 2 ^ 6 := by
            have h10 : x ≤ 6 := h8
            exact (Nat.pow_le_pow_of_le_right (by norm_num) h10)
          norm_num at h9
          omega  -- Contradiction with 2^x = 128
        have h8 : x = 7 := by
          omega
        exact h8
      exact h5
    exact h3
  · -- Backward direction: if x = 7, then 2^x + 2^x + 2^x + 2^x = 512
    intro h
    rw [h]
    norm_num