import Mathlib

theorem inequalities_603436 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x * y ≥ 1) :
    x ^ 3 + y ^ 3 + 4 * x * y ≥ x ^ 2 + y ^ 2 + x + y + 2 ∧
    2 * (x ^ 3 + y ^ 3 + x * y + x + y) ≥ 5 * (x ^ 2 + y ^ 2) := by
  constructor
  · -- Prove the first inequality
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1),
      sq_nonneg (x + y - 2), hxy, mul_pos hx hy, mul_nonneg (show (0 : ℝ) ≤ x - 0 by linarith) (show (0 : ℝ) ≤ y - 0 by linarith), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y by linarith)]
  · -- Prove the second inequality
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1),
      sq_nonneg (x + y - 2), hxy, mul_pos hx hy, mul_nonneg (show (0 : ℝ) ≤ x - 0 by linarith) (show (0 : ℝ) ≤ y - 0 by linarith), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y by linarith)]