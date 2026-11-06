import Mathlib

theorem number_theory_2106 :
    IsGreatest {n : ℤ | n ≤ 0} 0 := by 
  constructor
  · -- Show 0 is in the set
    simp
  · -- Show that if n ≤ 0, then n ≤ 0
    intro n hn
    simpa using hn