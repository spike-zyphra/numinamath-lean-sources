import Mathlib

theorem number_theory_5069 : IsLeast {x | ∃ a b, x = 3 + 5 * a ∧ x = 6 + 9 * b} 33 := by
  constructor
  · -- Show 33 is a member of the set
    use 6, 3
    all_goals norm_num
  · -- Show any element in the set is ≥ 33
    intro x hx
    rcases hx with ⟨a, b, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : a < 6 := by
      omega
    have h4 : b < 3 := by
      omega
    interval_cases a <;> interval_cases b <;> omega