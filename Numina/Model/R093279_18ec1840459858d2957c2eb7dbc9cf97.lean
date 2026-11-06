import Mathlib

theorem number_theory_235841 : IsLeast {x | 7 ∣ x ∧ x % 2 = 1 ∧ x % 3 = 1 ∧ x % 4 = 1 ∧ x % 5 = 1 ∧ x % 6 = 1} 301 := by
  constructor
  · -- Show 301 is in the set
    show 7 ∣ 301 ∧ 301 % 2 = 1 ∧ 301 % 3 = 1 ∧ 301 % 4 = 1 ∧ 301 % 5 = 1 ∧ 301 % 6 = 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show no smaller positive integer is in the set
    intro x hx
    rcases hx with ⟨h1, h2, h3, h4, h5, h6⟩
    omega