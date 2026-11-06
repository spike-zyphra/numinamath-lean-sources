import Mathlib

theorem number_theory_201851 : IsLeast {n | (Nat.digits 10 n).length = 2} 10 := by 
  constructor 
  · -- Show 10 is in the set
    show (Nat.digits 10 10).length = 2
    norm_num 
  · -- Show that it's the smallest
    intro n hn
    have h : (Nat.digits 10 n).length = 2 := hn 
    by_contra h'
    push_neg at h'
    interval_cases n <;> norm_num at h ⊢ <;> all_goals try { omega }