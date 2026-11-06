import Mathlib

theorem algebra_46 {x : ℕ} (hx : 2 ^ x + 2 ^ x + 2 ^ x + 2 ^ x = 128) : (x + 1) * (x - 1) = 24 := by
  have eq1 : 2 ^ x + 2 ^ x + 2 ^ x + 2 ^ x = 4 * (2 ^ x) := by
    ring
  rw [eq1] at hx
  have h2 : 2 ^ x = 32 := by 
    omega
  have h3 : x = 5 := by
    have h4 : 2 ^ x = 32 := h2
    have h5 : x = 5 := by
      have h6 : x ≤ 5 := by
        by_contra h
        push_neg at h
        have h7 : x ≥ 6 := by omega
        have h8 : 2 ^ x ≥ 64 := by
          have h9 : 2 ^ x ≥ 2 ^ 6 := by
            apply Nat.pow_le_pow_of_le_right
            norm_num
            all_goals linarith
          norm_num at h9 ⊢
          all_goals linarith
        have h10 : 2 ^ x = 32 := h4
        linarith
      have h7 : x ≥ 5 := by
        by_contra h
        push_neg at h
        have h8 : x ≤ 4 := by omega
        have h9 : 2 ^ x ≤ 16 := by
          have h10 : x ≤ 4 := by omega
          have h11 : 2 ^ x ≤ 2 ^ 4 := by
            apply Nat.pow_le_pow_of_le_right
            norm_num
            all_goals linarith
          norm_num at h11 ⊢
          all_goals linarith
        have h10 : 2 ^ x = 32 := h4
        linarith
      omega
    exact h5
  subst x
  all_goals norm_num