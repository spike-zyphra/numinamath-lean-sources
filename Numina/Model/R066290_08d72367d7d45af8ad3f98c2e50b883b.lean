import Mathlib

theorem number_theory_6301 : IsLeast {n | 0 < n ∧ 255 ∣ ∑ i in Finset.Icc 1 n, i} 50 := by
  constructor
  · -- Show that 50 is in the set: 0 < 50 and 255 divides the sum from 1 to 50
    constructor
    · norm_num
    · -- Calculate the sum from 1 to 50 and check divisibility
      native_decide
  · -- Show that 50 is the smallest. If n in the set, then n >= 50
    intro n hn
    have ⟨hn_pos, hn_div⟩ := hn
    by_contra h
    push_neg at h
    interval_cases n <;> try { contradiction }
    <;> norm_num [Finset.sum_Icc_succ_top] at hn_div <;> all_goals omega