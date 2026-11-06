import Mathlib

/- Find the fraction that equals $0.72\overline{6}$. -/
theorem algebra_22089 : 72 / 100 + 6 / 1000 * ∑' n : ℕ, (1 / 10 : ℝ) ^ n = 109 / 150 := by
  rw [tsum_geometric_of_lt_one (by linarith) (by linarith)]
  norm_num