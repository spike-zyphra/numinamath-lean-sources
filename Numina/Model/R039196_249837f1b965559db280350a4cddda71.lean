import Mathlib

theorem number_theory_98108 : IsLeast { N : ℕ | N > 0 ∧ ∃ a b c : ℕ, a < 8 ∧ b < 8 ∧ c < 8 ∧
    N = a * 11 ^ 2 + b * 11 + c ∧ N = 8 ^ 3 + b * 8 ^ 2 + c * 8 + a } 621 := by
  constructor
  · -- Show 621 is in the set
    constructor
    · norm_num
    · use 5, 1, 5
      all_goals norm_num
  · -- Show no smaller element is in the set
    intro N h
    rcases h with ⟨hN_pos, a, b, c, ha, hb, hc, h11, h8⟩
    by_contra h'
    push_neg at h'
    have h2 : a < 8 := by linarith
    have h3 : b < 8 := by linarith
    have h4 : c < 8 := by linarith
    interval_cases a <;> interval_cases b <;> omega