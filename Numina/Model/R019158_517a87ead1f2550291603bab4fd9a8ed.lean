import Mathlib

theorem algebra_602994 (x y : ℝ) (h : x^2 + y^2 - 4 * x - 6 * y + 9 = 0) :
    19 ≤ x^2 + y^2 + 12 * x + 6 * y ∧ x^2 + y^2 + 12 * x + 6 * y ≤ 99 := by
  have h1 : (x - 2) ^ 2 + (y - 3) ^ 2 = 4 := by
    nlinarith

  have h2 : -20 ≤ 8 * (x - 2) + 6 * (y - 3) := by
    nlinarith [sq_nonneg (8 * (y - 3) - 6 * (x - 2)), sq_nonneg (6 * (x - 2) - 8 * (y - 3)), sq_nonneg ((x - 2) * 8 - (y - 3) * 6)]

  have h3 : 8 * (x - 2) + 6 * (y - 3) ≤ 20 := by
    nlinarith [sq_nonneg (8 * (y - 3) - 6 * (x - 2)), sq_nonneg (6 * (x - 2) - 8 * (y - 3)), sq_nonneg ((x - 2) * 8 - (y - 3) * 6)]

  have h10 : 64 ≤ (x + 6) ^ 2 + (y + 3) ^ 2 := by
    nlinarith

  have h11 : (x + 6) ^ 2 + (y + 3) ^ 2 ≤ 144 := by
    nlinarith
  
  constructor
  · -- Prove $19 \leq x^2 + y^2 + 12 x + 6 y$.
    nlinarith
  · -- Prove $x^2 + y^2 + 12 x + 6 y \leq 99$.
    nlinarith