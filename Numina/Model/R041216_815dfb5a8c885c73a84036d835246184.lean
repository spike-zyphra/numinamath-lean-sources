import Mathlib

theorem algebra_293393 {a : ℕ → ℝ} (ha : ∀ n, ∑ i in Finset.range n, a i = -n^2 + 9 * n + 2) :
    (∀ n, a n = 9 - n) ∧
    (∃ m, 0 < m ∧ ∀ n, ∑ i in Finset.range n, (1 / ((i + 1) * (12 - a i))) < m / 32) ↔ m = 24 := by

  have h1 := ha 0
  norm_num [Finset.sum_range_zero] at h1
  all_goals linarith