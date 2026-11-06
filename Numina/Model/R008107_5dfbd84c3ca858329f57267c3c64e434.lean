import Mathlib

theorem number_theory_188906 :
    (2^2001) % 3 = 2 ∧ (2^2001) % 5 = 2 ∧ (2^2001) % 7 = 1 ∧ (2^2001) % 9 = 8 ∧
    (2^2001) % 11 = 2 ∧ (2^2001) % 13 = 5 ∧ (2^2001) % 15 = 2 ∧ (2^2001) % 17 = 2 := by 
  repeat { constructor }
  all_goals norm_num