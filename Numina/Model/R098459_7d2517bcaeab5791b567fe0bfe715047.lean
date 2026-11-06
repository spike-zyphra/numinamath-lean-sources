import Mathlib

theorem number_theory_140923 : IsLeast {x | x % 2 = 1 ∧ x % 5 = 2 ∧ x % 7 = 3 ∧ x % 9 = 4} 157 := by 
  constructor
  · constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 157 is the smallest
    intro x hx
    rcases hx with ⟨h2, h5, h7, h9⟩
    omega