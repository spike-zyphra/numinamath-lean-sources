import Mathlib

theorem algebra_4205 : (X^2 + X * Y - 6 * Y^2 + X + 13 * Y - 6 : MvPolynomial (Fin 2) ℝ) =
    (X + 3 * Y - 2) * (X - 2 * Y + 3) := by 
  ring_nf