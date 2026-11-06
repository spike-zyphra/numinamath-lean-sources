import Mathlib

theorem algebra_1496 (x y z : ℝ) : x^2 + y^2 + z^2 = 1 ∧ x + 2 * y + 3 * z = 4 → False:= by 
  intro h
  rcases h with ⟨h1, h2⟩
  nlinarith [sq_nonneg (x - 4 / 7), sq_nonneg (y - 8 / 7), sq_nonneg (z - 12 / 7),
            sq_nonneg (x + 2 * y + 3 * z - 4), sq_nonneg (x - z), sq_nonneg (y - 2 * z), sq_nonneg (x - 2 * y)]