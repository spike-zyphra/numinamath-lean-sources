import Mathlib

theorem number_theory_22695 :
    IsGreatest {x | x < 2010 ∧ x % 7 = 5 ∧ x % 11 = 10 ∧ x % 13 = 10} 1440 := by
  constructor
  · -- Show 1440 is in the set.
    refine' ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show any element in the set is ≤ 1440.
    intro x h
    rcases h with ⟨h1, h2, h3, h4⟩
    omega