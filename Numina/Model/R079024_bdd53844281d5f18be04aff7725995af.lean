import Mathlib

theorem number_theory_4633 : IsLeast {x | x % 7 = 1 ∧ x % 11 = 2 ∧ x % 13 = 3 ∧ x % 5 = 4} 3214 := by 
  constructor
  · -- Verify 3214 is in the set
    show 3214 % 7 = 1 ∧ 3214 % 11 = 2 ∧ 3214 % 13 = 3 ∧ 3214 % 5 = 4
    repeat { constructor }
    all_goals norm_num
  · -- Prove that 3214 is the smallest
    intro y hy
    have h1 : y % 7 = 1 := hy.1
    have h2 : y % 11 = 2 := hy.2.1
    have h3 : y % 13 = 3 := hy.2.2.1
    have h4 : y % 5 = 4 := hy.2.2.2
    omega