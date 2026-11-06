import Mathlib

theorem algebra_5445 (n : ℕ) (h : 0 < n) (h' : 2^12 / 2^n = 2^3) :
    n = 9 := by
  have h1 : n ≤ 12 := by
    by_contra h2
    push_neg at h2
    have h3 : 2 ^ 12 / 2 ^ n = 0 := by
      have h4 : 2 ^ 12 < 2 ^ n := by
        have h5 : n > 12 := h2
        have h6 : n ≥ 13 := by
          omega
        have h7 : 2 ^ 12 < 2 ^ 13 := by
          norm_num
        have h8 : 2 ^ 13 ≤ 2 ^ n := by
          apply Nat.pow_le_pow_of_le_right
          all_goals
          norm_num
          all_goals omega
        linarith
      rw [Nat.div_eq_zero_iff]
      omega
    rw [h3] at h'
    all_goals
    norm_num at h'
  interval_cases n <;> norm_num at h' <;> all_goals
  omega