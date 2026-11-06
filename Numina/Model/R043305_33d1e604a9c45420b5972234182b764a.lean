import Mathlib

theorem inequalities_1854 (a : ℝ) (ha : -1 ≤ a ∧ a ≤ 1) : (1 + abs a + a ^ 2) ^ 3 ≥ (1 + abs a) ^ 3 * (1 + abs a ^ 3) := by
  rcases ha with ⟨ha1, ha2⟩
  by_cases h : a ≥ 0
  · -- If a ≥ 0, then |a| = a
    have h1 : abs a = a := abs_of_nonneg h
    rw [h1]
    nlinarith [sq_nonneg (a ^ 2 - a ), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a ^ 2 - 1 ), sq_nonneg (a ^ 2 - a ), sq_nonneg (a * (a - 1)), sq_nonneg (a * (a + 1)), mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ a by linarith)]
  · -- If a < 0, then |a| = -a
    have h2 : abs a = -a := abs_of_neg (show a < 0 by linarith)
    rw [h2]
    nlinarith [sq_nonneg (a ^ 2 + a ), sq_nonneg (a + 1 ), sq_nonneg (-a - 1 ), sq_nonneg (a ^ 2 - 1 ), sq_nonneg (a ^ 2 - (-a) ), sq_nonneg (a * (a + 1)), sq_nonneg ((-a) * (a + 1)), sq_nonneg (a * (-a)), mul_nonneg (show 0 ≤ -a by linarith) (show 0 ≤ 1 + a by linarith)]