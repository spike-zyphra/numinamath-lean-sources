import Mathlib

theorem number_theory_12589 : IsLeast {n : ℕ | 100 ≤ n ∧ n < 1000 ∧ (n + 5) % 8 = 0 ∧ (n - 8) % 5 = 0} 123 := by
  constructor
  · -- Show that 123 is indeed in the set.
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 123 is the smallest element in the set.
    intro n hn
    rcases hn with ⟨hn100, hn1000, h1, h2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> omega