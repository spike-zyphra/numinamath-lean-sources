import Mathlib

theorem number_theory_194930 : IsLeast {d | d % 7 = 1 ∧ d % 5 = 2 ∧ d % 3 = 2} 92 := by 
  constructor
  · -- Show 92 satisfies all three congruences 
    show 92 % 7 = 1 ∧ 92 % 5 = 2 ∧ 92 % 3 = 2
    norm_num
  · -- Show that 92 is the smallest
    intro d hd
    rcases hd with ⟨h1, h2, h3⟩
    omega