import Mathlib

theorem number_theory_449 : IsLeast {n : ℕ | (n + (n + 1) + (n + 2)) % 10000 = 2011} 7336 := by
  constructor
  · -- Show that 7336 is in the set
    show (7336 + (7336 + 1) + (7336 + 2)) % 10000 = 2011
    norm_num
  · -- Show that any number in the set is greater than or equal to 7336
    intro n hn
    have h : (n + (n + 1) + (n + 2)) % 10000 = 2011 := hn
    omega