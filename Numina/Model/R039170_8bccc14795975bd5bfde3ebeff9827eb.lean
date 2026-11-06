import Mathlib

theorem number_theory_302345 :
    IsLeast {a : ℕ | 0 < a ∧ ∃ b, 0 < b ∧ 1176 * a = b ^ 4} 2646 := by
  constructor
  · -- Show 2646 is in the set.
    constructor
    · -- Show 2646 > 0.
      norm_num
    · -- Show there exists a b such that 1176 * 2646 = b ^ 4
      use 42
      all_goals norm_num
  · -- Show 2646 is the least.
    intro a ha
    rcases ha with ⟨ha_pos, b, hb_pos, heq⟩
    by_contra h
    push_neg at h
    have h1 : a < 2646 := by linarith
    have h2 : b ≤ 41 := by
      by_contra h3
      push_neg at h3
      have h3 : b ≥ 42 := by omega
      have h4 : b ^ 4 ≥ 42 ^ 4 := by
        have hb4 : b ≥ 42 := h3
        have h5 : b ^ 4 ≥ 42 ^ 4 := by
          apply Nat.pow_le_pow_of_le_left hb4 4
        linarith
      have h6 : 1176 * a ≥ 42 ^ 4 := by linarith [heq, h4]
      nlinarith
    interval_cases b <;> omega