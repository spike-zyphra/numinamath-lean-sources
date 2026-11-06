import Mathlib

theorem number_theory_13320 :
    IsLeast {x | (x ^ 3) % 10000 = 2021} 1741 := by
  constructor
  · -- Show that 1741 is indeed in the set
    norm_num
  · -- Show that 1741 is the minimum
    intro y hy
    have h : y ^ 3 % 10000 = 2021 := hy
    by_contra h'
    push_neg at h'
    interval_cases y <;> norm_num at h <;> omega