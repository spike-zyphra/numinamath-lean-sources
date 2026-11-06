import Mathlib

theorem number_theory_126679 :
    IsLeast {n | 13 ∣ (5^n + n^5)} 12 := by 
  constructor 
  · -- Show 12 is indeed in the set 
    norm_num
  · -- Show no smaller natural number is in the set 
    intro n hn 
    have h : 13 ∣ (5 ^ n + n ^ 5) := hn
    by_contra h'
    push_neg at h'
    have h1 : n < 12 := by linarith 
    interval_cases n <;> norm_num at h <;> omega