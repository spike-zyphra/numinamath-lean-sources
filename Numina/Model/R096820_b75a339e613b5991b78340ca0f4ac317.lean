import Mathlib

theorem algebra_308604 (x y z : ℝ) (h₀ : x + y + z = 0) (h₁ : (x - y)^2 + (y - z)^2 + (z - x)^2 ≤ 2) :
    -2/3 ≤ x ∧ x ≤ 2/3 := by
  have h2 : z = -x - y := by
    linarith
  have h3 : (x - y)^2 + (y - z)^2 + (z - x)^2 = 6 * (x^2 + x * y + y^2) := by
    rw [h2]
    nlinarith
  have h4 : x^2 + x * y + y^2 ≤ (1 / 3 : ℝ) := by
    nlinarith [h₁, h3]
  constructor
  · -- Prove that $-2/3 \leq x$
    nlinarith [sq_nonneg (y + x / 2), sq_nonneg (y - x / 2), sq_nonneg (y + (1 / 3)), sq_nonneg (x + 2 / 3), sq_nonneg (x - 2 / 3), sq_nonneg (y - (1 / 3))]
  · -- Prove that $x \leq 2/3$
    nlinarith [sq_nonneg (y + x / 2), sq_nonneg (y - x / 2), sq_nonneg (y + (1 / 3)), sq_nonneg (x + 2 / 3), sq_nonneg (x - 2 / 3), sq_nonneg (y - (1 / 3))]