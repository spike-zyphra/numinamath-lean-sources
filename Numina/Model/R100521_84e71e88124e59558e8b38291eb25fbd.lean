import Mathlib

theorem number_theory_4845 (n : ℕ) (hn : n > 0) :
    IsLeast {n | 0 < n ∧ 2023 ∣ ∑ i in Finset.Icc 1 n, i^3} 34 := by
  constructor
  · -- Show that 34 is in the set, i.e., 0 < 34 and 2023 divides the sum of cubes from 1 to 34
    constructor
    · -- Show 0 < 34
      norm_num
    · -- Show 2023 divides the sum of cubes from 1 to 34
      native_decide
  · -- Show that 34 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    interval_cases n <;> try { norm_num [Finset.sum_Icc_succ_top] at hn_div <;> all_goals omega }
    <;> try { contradiction }