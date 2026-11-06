import Mathlib

theorem number_theory_271253 : IsLeast {n | (n.divisors.card = 20)} 240 := by 
  constructor 
  · -- Show 240 is in the set 
    native_decide
  · -- Show 240 is minimal
    intro n hn 
    have h : n.divisors.card = 20 := by 
      simpa using hn
    by_contra h1 
    push_neg at h1
    interval_cases n <;> try { contradiction }
    <;> try { 
      all_goals 
      try native_decide 
      all_goals 
      omega 
    }