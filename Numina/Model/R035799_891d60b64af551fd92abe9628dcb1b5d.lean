import Mathlib

theorem number_theory_610762 :
    ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ IsSquare (x + y) ∧ IsSquare (x ^ 2 + y ^ 2) ∧ IsSquare (x ^ 3 + y ^ 3) := by
  use 184, 345
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · -- Show that x + y is a perfect square
    native_decide
  constructor
  · -- Show that x² + y² is a perfect square
    native_decide
  · -- Show that x³ + y³ is a perfect square
    native_decide