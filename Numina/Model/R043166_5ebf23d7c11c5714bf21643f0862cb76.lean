import Mathlib

theorem number_theory_3902 : IsLeast {a : ℕ | a > 0 ∧ ∃ b : ℕ, b > 0 ∧ 2023 * a = b ^ 3} 833 := by
  constructor
  · -- Show 833 is in the set
    constructor
    · norm_num
    · -- Show existence of b
      use 119
      all_goals norm_num
  · -- Show no smaller element is in the set
    intro a ha
    rcases ha with ⟨ha_pos, ⟨b, hb_pos, h_eq⟩⟩
    by_contra h
    push_neg at h
    -- We need to show a contradiction
    -- From h: a < 833
    -- From h_eq: 2023 * a = b ^ 3
    -- We can deduce b^3 < 2023 * 833
    have h1 : b ≤ 119 := by
      by_contra h2
      push_neg at h2
      have h2 : b ≥ 120 := by omega
      have h3 : b ^ 3 ≥ 120 ^ 3 := by
        have h4 : b ≥ 120 := by linarith
        have h5 : b ^ 3 ≥ 120 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals linarith
        linarith
      have h4 : a < 833 := by linarith
      nlinarith
    interval_cases b <;> omega