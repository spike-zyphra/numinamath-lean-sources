import Mathlib

theorem number_theory_5797 :
  IsLeast {n | 0 < n ∧ 2019 ∣ ∑ i in Finset.Icc 1 n, i} 672 := by
  constructor
  · -- Show that 672 is in the set
    constructor
    · -- Show 672 > 0
      norm_num
    · -- Show the divisibility
      native_decide
  · -- Show that 672 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h1 : n ≤ 671 := by linarith
    have h3 : ¬ (2019 ∣ ∑ i in Finset.Icc 1 n, i) := by
      interval_cases n <;> native_decide
    contradiction