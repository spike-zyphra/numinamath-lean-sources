import Mathlib

theorem number_theory_8670 :
  IsLeast {n : ℕ | 0 < n ∧ (Nat.divisors n).card ≥ 24} 360 := by 
  constructor
  · -- First, show that 360 is indeed in the set (i.e., it's a positive integer with at least 24 divisors)
    constructor
    · -- Show that 360 is positive
      norm_num
    · -- Show that the number of divisors of 360 is at least 24
      native_decide
  · -- Now, need to show that 360 is the smallest such element
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    interval_cases n <;> try { contradiction }
    <;> try { native_decide }