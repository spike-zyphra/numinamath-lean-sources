import Mathlib

theorem number_theory_121760 {n : ℕ} (hn : n = 2007 ∨ n = 1011) :
    ∃ k, n = k + (k + 1) ∧ ∃ m, n = m + (m + 1) + (m + 2) := by 
  rcases hn with (rfl | rfl)
  · -- Let's handle 2007
    use 1003
    constructor
    · -- Show 2007 = 1003 + (1003 + 1)
      norm_num
    · -- Find m such that 2007 = m + (m + 1) + (m + 2)
      use 668
      all_goals norm_num
  · -- Let's handle 1011
    use 505
    constructor
    · -- Show 1011 = 505 + (505 + 1)
      norm_num
    · -- Find m such that 1011 = m + (m + 1) + (m + 2)
      use 336
      all_goals norm_num