import Mathlib

theorem number_theory_284286 :
    IsLeast {n | (n * 7) % 10000 = 2012} 1716 := by
  constructor
  · -- Show that 1716 is in the set
    norm_num
  · -- Show that any number in the set is ≥ 1716
    intro n hn
    have h1 : (n * 7) % 10000 = 2012 := hn
    by_contra h
    push_neg at h
    have h2 : n < 1716 := h
    interval_cases n <;> norm_num at h1 <;> all_goals omega