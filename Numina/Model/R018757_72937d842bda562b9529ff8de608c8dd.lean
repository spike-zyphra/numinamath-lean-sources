import Mathlib

theorem algebra_4432 (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y)
    (hxy : x + 2 * y = 1 / 2) :
    8 * x * y + 4 * y ^ 2 + 1 ≤ 4 / 3 ∧
    8 * x * y + 4 * y ^ 2 + 1 ≥ 1 / 3 := by
  have hx_eq : x = 1 / 2 - 2 * y := by
    linarith
  have h1 : 8 * x * y + 4 * y ^ 2 + 1 = -12 * y ^ 2 + 4 * y + 1 := by
    rw [hx_eq]
    nlinarith
  constructor
  · -- Prove that $8xy + 4y^2 + 1 \leq \frac{4}{3}$
    nlinarith [sq_nonneg (y - 1 / 6)]
  · -- Prove that $8xy + 4y^2 + 1 \geq \frac{1}{3}$
    nlinarith [sq_nonneg (y - 2 / 3), sq_nonneg (x - 1 / 6), sq_nonneg (y), sq_nonneg (x)]