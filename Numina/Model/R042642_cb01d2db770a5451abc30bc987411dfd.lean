import Mathlib

open Finset Nat Pointwise

theorem number_theory_54581 :
    IsLeast {n : ℕ | (n.divisors.filter Odd).card = 6 ∧ (n.divisors.filter Even).card = 12} 180 := by
  constructor
  · -- Show 180 is in the set
    native_decide
  · -- Show 180 is the least
    intro n hn
    rcases hn with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> try { contradiction }