import Mathlib

theorem number_theory_233499 (a : ℕ → ℝ) (ha : ∀ n, a n = a (n - 1) + 2 * Real.sqrt (n + 1)) :
    IsGreatest {x | ∃ n, x = a n ∧ n ≤ 7} 25 := by
  have h8 := ha 0
  norm_num at h8
  all_goals linarith