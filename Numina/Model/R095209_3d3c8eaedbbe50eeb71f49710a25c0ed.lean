import Mathlib

theorem algebra_292105 :
    ¬∃ m n : ℝ, (3 * m ^ 2 + 4 * m * n - 2 * n ^ 2 < 0) ∧ (-m ^ 2 - 4 * m * n + 3 * n ^ 2 < 0) := by
  rintro ⟨m, n, h1, h2⟩
  have h3 : 3 * m ^ 2 + 4 * m * n - 2 * n ^ 2 + (-m ^ 2 - 4 * m * n + 3 * n ^ 2) < 0 := by linarith
  have h4 : 3 * m ^ 2 + 4 * m * n - 2 * n ^ 2 + (-m ^ 2 - 4 * m * n + 3 * n ^ 2) = 2 * m ^ 2 + n ^ 2 := by
    ring
  rw [h4] at h3
  have h5 : 2 * m ^ 2 + n ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (m), sq_nonneg (n)]
  linarith