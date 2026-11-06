import Mathlib

theorem algebra_14150 (x : ℕ) (h : 2 * (3 ^ x) = 162) : x = 4 := by
  have h1 : 3 ^ x = 81 := by
    omega
  have h4 : x = 4 := by
    have h3 : 3 ^ x = 81 := h1
    have h6 : x ≤ 4 := by
      by_contra h
      push_neg at h
      have h7 : x ≥ 5 := by
        omega
      have h8 : 3 ^ x ≥ 3 ^ 5 := by
        apply pow_le_pow_right
        all_goals linarith
      have h9 : 3 ^ 5 = 243 := by
        norm_num
      have h10 : 3 ^ x ≥ 243 := by
        linarith [h8, h9]
      linarith [h3, h10]
    interval_cases x <;> omega
  exact h4