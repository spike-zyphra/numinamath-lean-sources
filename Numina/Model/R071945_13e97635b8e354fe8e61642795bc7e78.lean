import Mathlib

theorem algebra_284074 (x : ℕ) (hx : 10^x - 10 = 9990) : x = 4 := by
  have h1 : 10^x = 10000 := by
    omega
  have h2 : x = 4 := by
    have h3 : 10 ^ x = 10000 := h1
    have h4 : x = 4 := by
      have h5 : x ≤ 4 := by
        by_contra h
        push_neg at h
        have h6 : x ≥ 5 := by
          omega
        have h7 : 10 ^ x ≥ 10 ^ 5 := by
          apply pow_le_pow_right
          all_goals norm_num
          all_goals omega
        norm_num [h3] at h7
        all_goals linarith
      have h8 : x ≥ 4 := by
        by_contra h
        push_neg at h
        have h9 : x ≤ 3 := by
          omega
        have h10 : 10 ^ x ≤ 10 ^ 3 := by
          apply pow_le_pow_right
          all_goals norm_num
          all_goals omega
        norm_num [h3] at h10
        all_goals linarith
      have h9 : x = 4 := by
        omega
      exact h9
    exact h4
  exact h2