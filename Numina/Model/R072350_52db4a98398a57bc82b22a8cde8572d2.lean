import Mathlib

theorem number_theory_268262 : IsLeast {n : ℕ | 0 < n ∧ (3 ∣ n) ∧ (5 ∣ n) ∧ (7 ∣ n) ∧ (9 ∣ n)} 315 := by
  constructor
  · -- Verify 315 is in the set.
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show that 315 is the least in the set
    intro n hn
    rcases hn with ⟨hn_pos, h3, h5, h7, h9⟩
    by_contra h
    push_neg at h
    interval_cases n <;> omega