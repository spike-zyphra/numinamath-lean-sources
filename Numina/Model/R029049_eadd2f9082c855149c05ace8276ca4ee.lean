import Mathlib

  theorem number_theory_72245 :
    IsLeast {n | n.divisors.card = 16 ∧ n > 0} 120 := by
  constructor
  · -- Show 120 is in the set
    constructor
    · -- Show that 120 has exactly 16 divisors
      native_decide
    · -- Show 120 > 0
      norm_num
  · -- Show there is no smaller n in the set
    intro n hn
    rcases hn with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> try { contradiction }