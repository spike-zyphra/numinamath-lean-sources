import Mathlib

theorem inequalities_250136 (x y z : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    2 * (x ^ 3 + y ^ 3 + z ^ 3) - (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) ≤ 3 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  rcases hz with ⟨hz1, hz2⟩
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ 1 - x by linarith),
          mul_nonneg (show (0 : ℝ) ≤ y by linarith) (show (0 : ℝ) ≤ 1 - y by linarith),
          mul_nonneg (show (0 : ℝ) ≤ z by linarith) (show (0 : ℝ) ≤ 1 - z by linarith)]