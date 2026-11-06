import Mathlib

theorem number_theory_188669 :
    IsLeast {n : ℕ | 0 < n ∧ 100 ∣ ∑ i in Finset.Icc 1 n, i^2} 24 := by
  constructor
  · -- Show that 24 is in the set
    constructor
    · norm_num
    · -- Check divisibility
      native_decide
  · -- Show that any element in the set is ≥ 24
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    interval_cases n <;> try { contradiction <;> try { contradiction <;> try { contradiction } } }
    <;> norm_num [Finset.sum_Icc_succ_top] at hn_div <;> try { omega }
    <;> try { contradiction }
    <;> omega