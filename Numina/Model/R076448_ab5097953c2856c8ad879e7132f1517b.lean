import Mathlib

theorem number_theory_232606 : IsGreatest {n | n / 31 = 30} 960 := by 
  constructor
  · -- Show that 960 is in the set
    norm_num
  · -- Show that 960 is the greatest element in the set
    intro n hn
    have h : n / 31 = 30 := hn
    by_contra h'
    push_neg at h'
    -- Suppose n > 960, then n >= 961
    -- If n >= 961, then n / 31 >= 31
    -- But n / 31 = 30 contradicts
    omega