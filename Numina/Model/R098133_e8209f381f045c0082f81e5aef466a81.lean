import Mathlib

theorem number_theory_114708 : ¬ ∃ x y : ℤ, 21 * x - 35 * y = 59 := by 
  rintro ⟨x, y, h⟩
  omega