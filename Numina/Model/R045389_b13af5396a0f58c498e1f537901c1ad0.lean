import Mathlib

theorem number_theory_254385 :
    IsLeast { x : ℕ | 5 ^ x  > 7812500 } 10 := by 
  constructor 
  · -- Show 10 is in the set 
    norm_num 
  · -- Show no smaller element is in the set 
    intro x h 
    have h1 : 5 ^ x > 7812500 := by 
      simpa using h 
    by_contra h2 
    push_neg at h2 
    have h2' : x < 10 := by 
      omega 
    interval_cases x <;> norm_num at h1