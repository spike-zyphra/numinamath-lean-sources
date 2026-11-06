import Mathlib

theorem inequalities_93589 (n : ℕ) :
    IsGreatest {n | 7 * n < 100} 14 := by 
  constructor 
  · -- Show that 14 is in the set
    show 7 * 14 < 100
    norm_num 
  · -- Show that 14 is the greatest in the set
    intro n hn 
    have h : 7 * n < 100 := by 
      simpa using hn 
    by_contra h' 
    push_neg at h' 
    have h1 : n ≥ 15 := by 
      omega 
    have h2 : 7 * n ≥ 105 := by 
      omega 
    linarith