import Mathlib

theorem number_theory_4146 (A : ℕ) : A ^ 3 = 8230172859 → A = 2019 := by
  intro h
  have h1 : A ≤ 2019 := by
    by_contra h2
    push_neg at h2
    have h3 : A ^ 3 > 2019 ^ 3 := by
      have h4 : A > 2019 := by linarith
      have h5 : A ^ 3 > 2019 ^ 3 := by
        apply Nat.pow_lt_pow_left
        all_goals linarith
      exact h5
    have h6 : 2019 ^ 3 = 8230172859 := by norm_num
    nlinarith [h, h6]
  have h7 : A ≥ 2019 := by
    by_contra h4
    push_neg at h4
    have h5 : A ^ 3 < 2019 ^ 3 := by
      have h6 : A < 2019 := by linarith
      have h7 : A ^ 3 < 2019 ^ 3 := by
        apply Nat.pow_lt_pow_left
        all_goals linarith
      exact h7
    have h8 : 2019 ^ 3 = 8230172859 := by norm_num
    nlinarith [h, h8]
  linarith