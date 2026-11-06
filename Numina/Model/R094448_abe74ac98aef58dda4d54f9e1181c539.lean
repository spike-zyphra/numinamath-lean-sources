import Mathlib

theorem number_theory_4001 :
    IsLeast {n | n > 0 ∧ n.divisors.card = 24} 360 := by
  constructor
  · -- Show that 360 is in the set
    constructor
    · norm_num
    · -- Show 360 has 24 divisors
      native_decide
  · -- Show no smaller element is in the set
    intro n hn
    have ⟨hn_pos, hn_div⟩ := hn
    by_contra h
    push_neg at h
    interval_cases n <;> try { contradiction }
    <;> try { native_decide }