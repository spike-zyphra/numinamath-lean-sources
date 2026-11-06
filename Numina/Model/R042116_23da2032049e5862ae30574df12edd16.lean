import Mathlib

theorem number_theory_22756 : IsLeast {n | ∃p, n = 7 * p ∧ 200 < n + 53 ∧ 8 ∣ n + 53 } 203 := by 
  constructor
  · -- Prove 203 is in the set
    use 29
    all_goals norm_num 
  · -- Prove 203 is the smallest 
    intro n hn 
    rcases hn with ⟨p, rfl, h1, h2⟩ 
    omega