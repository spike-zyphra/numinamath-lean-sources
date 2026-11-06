import Mathlib

theorem number_theory_19486 :
    IsLeast {n | Nat.Prime n ∧ Nat.Prime (∑ d in (∑ d in n.divisors, d).divisors, d)} 3 := by
  constructor
  · -- We verify that 3 is indeed in the set.
    constructor
    · norm_num
    · native_decide
  · -- We verify that 3 is the smallest element in the set.
    intro n hn
    rcases hn with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : n < 3 := h
    have h4 : n = 0 ∨ n = 1 ∨ n = 2 := by
      interval_cases n <;> try tauto
    rcases h4 with (rfl | rfl | rfl)
    · -- Case n = 0
      norm_num at h1 h2
    · -- Case n = 1
      norm_num at h1 h2
    · -- Case n = 2
      norm_num at h1 h2