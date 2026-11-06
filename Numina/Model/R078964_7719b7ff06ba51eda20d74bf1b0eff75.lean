import Mathlib

theorem number_theory_347 :
    IsLeast {x | ∃ a b, x = a * 2 + 1 ∧ x = b * 3 + 2} 5 := by
  constructor
  · -- To prove 5 is in the set, we need to find natural numbers a and b such that:
    -- 5 = a * 2 + 1 and 5 = b * 3 + 2
    use 2
    use 1
    all_goals norm_num
  · -- Now we need to show that 5 is the smallest such element in the set
    intro x h
    rcases h with ⟨a, b, ha, hb⟩
    omega