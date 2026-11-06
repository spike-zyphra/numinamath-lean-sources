import Mathlib

theorem number_theory_296643 : ¬ ∃ x y : ℤ, 6 * x + 3 * y = 17 := by 
  rintro ⟨x, y, h⟩
  omega