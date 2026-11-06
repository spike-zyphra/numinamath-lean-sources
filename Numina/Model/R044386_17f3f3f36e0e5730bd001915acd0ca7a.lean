import Mathlib

theorem number_theory_55134 : IsLeast {k | 0 < k ∧ 200 ∣ ∑ i in Finset.Icc 1 k, i^2} 112 := by
  constructor
  · -- Show that 112 is indeed in the set.
    constructor
    · norm_num
    · native_decide
  · -- Show that 112 is the smallest element in the set.
    intro k hk
    rcases hk with ⟨hk_pos, hk_div⟩
    by_contra h
    push_neg at h
    interval_cases k <;> try { contradiction }