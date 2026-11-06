import Mathlib

theorem number_theory_19430 :
    IsLeast {x | 1 < x ∧ ∏ d ∈ x.divisors, d = x ^ 6} 60 := by
  constructor
  · -- Verify that 60 is in the set
    constructor
    · -- Show 60 > 1
      norm_num
    · -- Show the product of the divisors of 60 is 60^6
      native_decide
  · -- Show no smaller element is in the set
    intro x h
    rcases h with ⟨hx1, hx2⟩
    by_contra h
    push_neg at h
    interval_cases x <;> try { contradiction }
    <;> try { 
      all_goals 
      try { 
        contradiction 
      } 
    }
    <;> try { 
      all_goals 
      native_decide 
    }