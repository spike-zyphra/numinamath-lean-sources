import Mathlib

theorem number_theory_218216 : IsLeast {n | 2015 < n ∧ (n % 6 = 0 ∧ n % 35 = 0)} 2100 := by 
  constructor
  · -- Show that 2100 is in the set
    constructor
    · -- 2100 > 2015
      norm_num
    constructor
    · -- 2100 % 6 = 0
      norm_num
    · -- 2100 % 35 = 0
      norm_num
  · -- Show that for any n in the set, 2100 ≤ n
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    omega