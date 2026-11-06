import Mathlib

theorem number_theory_303123 (k : ℤ) (h : ∃ m : ℤ, m^2 + (k - 4)*m + k = 0) :
    ∃ P A B C : ℤ, P > 0 ∧ A > 0 ∧ B > 0 ∧ C > 0 ∧
      P - A = 2 ∧ P - B = 1 ∧ P - C = 4 := by

  use 5, 3, 4, 1 
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
  constructor
  · norm_num 
  · norm_num