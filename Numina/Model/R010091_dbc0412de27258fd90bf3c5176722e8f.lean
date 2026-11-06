import Mathlib

theorem number_theory_15697 :
    IsLeast {n | 0 < n ∧ (n.divisors.card = 14)} 192 := by 
  constructor
  · -- Show 192 is in the set
    constructor
    · -- Show 192 is a positive integer
      norm_num 
    · -- Lean can compute that 192 has exactly 14 divisors
      native_decide 
  · -- Show that 192 is the smallest
    intro n hn
    have ⟨hn_pos, hn_div⟩ := hn
    by_contra h
    push_neg at h
    interval_cases n <;> try try { contradiction }
    <;> try try { native_decide }