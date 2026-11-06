import Mathlib

theorem number_theory_4525 : IsLeast {x : ℕ | x % 3 = 1 ∧ x % 5 = 2 ∧ x % 7 = 5 ∧ x % 11 = 2} 607 := by 
  constructor
  · -- Verify that 607 belongs to the set
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show that for all numbers in the set, they must be greater than or equal to 607
    intro y h
    rcases h with ⟨h1, h2, h3, h4⟩
    by_contra h'
    push_neg at h'
    interval_cases y <;> omega