import Mathlib

open Finset

theorem algebra_20930 : IsGreatest {k | ∃ m n : ℕ, 4 * m + 5 * n = 2007 ∧ k = (m - 1) * (n - 1)} 49896 := by
  constructor
  · -- Show that 49896 is in the set
    use 253, 199
    all_goals
      norm_num
  · -- Show that 49896 is the greatest element in the set
    intro k hk
    rcases hk with ⟨m, n, h1, h2⟩
    by_contra h3
    push_neg at h3
    have h3' : k > 49896 := by linarith
    have h4 : (m - 1) * (n - 1) > 49896 := by linarith [h2, h3']
    have h5 : m ≤ 501 := by
      omega
    have h6 : n ≤ 401 := by
      omega
    interval_cases m <;> omega