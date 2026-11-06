import Mathlib

theorem algebra_297007 {n : ℕ} (hn : n = 29999) :
    ∃ k, n = k * (k + 1) + (k + 1) * (k + 2) + k * (k + 2) := by
  rw [hn]
  use 99
  all_goals
    norm_num