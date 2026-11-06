import Mathlib


theorem number_theory_15521
    (is_abundant : ℕ → Prop)
    (def_isabundant : is_abundant = fun n => n < n.properDivisors.sum id) :
    IsLeast {n | is_abundant n} 12 := by
  rw [def_isabundant] at *
  constructor 
  · -- Show 12 is in the set
    native_decide
  · -- Show there is no smaller element in the set
    intro n hn
    have h : n < n.properDivisors.sum id := hn
    by_contra h'
    push_neg at h'
    interval_cases n <;> try { contradiction }
    all_goals
      try { 
        contradiction 
        <;> tauto 
        <;> native_decide
      }