import Mathlib

theorem algebra_5727 : (X^2 - Y^2 - 6 * Y - 9 : MvPolynomial (Fin 2) ℝ) =
    (X - Y - 3) * (X + Y + 3) := by 
  ring