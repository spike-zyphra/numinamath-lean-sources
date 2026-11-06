import Mathlib

open Nat BigOperators

theorem number_theory_340 :
    IsLeast {n : ℕ | n < ∑ d in n.properDivisors, d} 12 := by
  constructor
  · -- Show 12 is in the set.
    dsimp
    native_decide
  · -- Show there is no smaller element in the set.
    intro n hn
    dsimp at hn
    by_contra h
    push_neg at h
    interval_cases n <;> try { contradiction }
    <;> try { 
      native_decide 
    }