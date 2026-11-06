import Mathlib

theorem number_theory_98037 :
IsLeast {k : ℕ | 0 < k ∧ 200 ∣ ∑ i in Finset.Icc 1 k, i ^ 2} 112 := by
  constructor
  · -- Show 112 in the set
    constructor
    · norm_num
    · native_decide
  · -- Second part: minimality
    intro k hk
    rcases hk with ⟨hk_pos, hk_div⟩
    by_contra h
    push_neg at h
    interval_cases k <;> try { contradiction }