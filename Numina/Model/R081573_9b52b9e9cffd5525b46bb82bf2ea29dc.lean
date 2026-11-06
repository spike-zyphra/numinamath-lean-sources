import Mathlib

theorem number_theory_253536 :
    IsLeast {n | ∃ k l, n = k + l ∧ k * 6 + l * 7 = 200} 29 := by
  constructor
  · -- Show 29 is in the set
    use 3, 26
    all_goals norm_num
  · -- Show there is no smaller number in the set
    intro n hn
    rcases hn with ⟨k, l, h_eq, h_200⟩
    omega