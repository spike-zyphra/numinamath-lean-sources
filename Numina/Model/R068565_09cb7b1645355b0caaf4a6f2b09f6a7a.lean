import Mathlib

theorem number_theory_188288 : IsLeast {n | n % 5 = 2 ∧ n % 7 = 3 ∧ n % 11 = 7} 227 := by
  constructor
  · -- Show 227 is in the set
    show 227 % 5 = 2 ∧ 227 % 7 = 3 ∧ 227 % 11 = 7
    norm_num
  · -- Show that 227 is the smallest
    intro n hn
    rcases hn with ⟨h1, h2, h3⟩
    by_contra h
    push_neg at h
    -- Assume n is a natural number that satisfies all the conditions and n < 227
    have h4 : n < 227 := by
      omega
    -- With the conditions given, this is going to be false, as we'll get a contradiction
    interval_cases n <;> omega