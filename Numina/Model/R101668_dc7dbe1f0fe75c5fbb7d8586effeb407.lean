import Mathlib

theorem number_theory_171364 :
    ∃ a : ℤ, (∃ m : ℤ, m^2 = 16 + a) ∧ (∃ n : ℤ, n^2 = 3 + a) ∧ (∃ p : ℤ, p^2 = 16 * 3 + a) := by 
  use 33
  constructor
  · -- Show that there exists an integer m such that m^2 = 16 + 33
    use 7
    all_goals norm_num 
  constructor
  · -- Show that there exists an integer n such that n^2 = 3 + 33
    use 6
    all_goals norm_num 
  · -- Show that there exists an integer p such that p^2 = 16 * 3 + 33
    use 9
    all_goals norm_num