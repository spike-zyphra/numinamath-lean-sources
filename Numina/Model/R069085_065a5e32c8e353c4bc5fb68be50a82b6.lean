import Mathlib

theorem algebra_307744 (x y z a : ℝ) (ha : 0 ≤ a) (h1 : x + y + z = a)
    (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 1 / 2 * a ^ 2) :
    0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x ≤ 2 / 3 * a ∧ y ≤ 2 / 3 * a ∧ z ≤ 2 / 3 * a := by
  constructor
  · -- Prove 0 ≤ x
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h1, h2, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  constructor
  · -- Prove 0 ≤ y
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h1, h2, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  constructor
  · -- Prove 0 ≤ z
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h1, h2, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  constructor
  · -- Prove x ≤ 2/3 * a
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h1, h2, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  constructor
  · -- Prove y ≤ 2/3 * a
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h1, h2, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  · -- Prove z ≤ 2/3 * a
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h1, h2, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]