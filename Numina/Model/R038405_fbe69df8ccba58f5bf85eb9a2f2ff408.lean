import Mathlib

theorem number_theory_13782 :
    IsLeast {k : ℕ | 0 < k ∧ 200 ∣ ∑ i in Finset.Icc 1 k, i^2} 112 := by
  constructor
  · -- Show 112 is in the set
    constructor
    · -- Show 112 > 0
      norm_num
    all_goals native_decide
  · -- Show there is no smaller element in the set
    intro k hk
    rcases hk with ⟨hk_pos, hk_div⟩
    by_contra h
    push_neg at h
    interval_cases k <;> try { contradiction }
    <;> try { native_decide }