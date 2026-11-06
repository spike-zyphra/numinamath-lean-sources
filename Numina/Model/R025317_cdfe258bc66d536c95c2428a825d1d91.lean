import Mathlib

theorem algebra_403 (m n : ℝ) (h : ∃ x y, x + 3 * y = 2 * n - 1 ∧ 2 * x - y = m + 1 ∧ -1 ≤ x ∧ x ≤ 1 ∧ 1 ≤ y ∧ y ≤ 2) :
    100 / 17 ≤ m ^ 2 + n ^ 2 ∧ m ^ 2 + n ^ 2 ≤ 34 := by
  rcases h with ⟨x, y, h1, h2, hx1, hx2, hy1, hy2⟩
  have eq1 : n = (x + 3 * y + 1) / 2 := by
    linarith
  have eq2 : m = 2 * x - y - 1 := by
    linarith
  rw [show m ^ 2 + n ^ 2 = (2 * x - y - 1) ^ 2 + ((x + 3 * y + 1) / 2) ^ 2 by
    rw [eq2, eq1]
  ]
  constructor
  · -- Prove the minimum.
    nlinarith [sq_nonneg (x - 10 / 17), sq_nonneg (y - 7 / 17),
      sq_nonneg ((x + 3 * y + 1) / 2 - 10 / 17), sq_nonneg (2 * x - y - 1 + 10 / 17),
      mul_nonneg (show (0 : ℝ) ≤ x + 1 by linarith) (show (0 : ℝ) ≤ 1 - x by linarith),
      mul_nonneg (show (0 : ℝ) ≤ y - 1 by linarith) (show (0 : ℝ) ≤ 2 - y by linarith)]
  · -- Prove the maximum.
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 2),
      sq_nonneg ((x + 3 * y + 1) / 2 - 3), sq_nonneg (2 * x - y - 1 + 5),
      mul_nonneg (show (0 : ℝ) ≤ x + 1 by linarith) (show (0 : ℝ) ≤ 1 - x by linarith),
      mul_nonneg (show (0 : ℝ) ≤ y - 1 by linarith) (show (0 : ℝ) ≤ 2 - y by linarith)]