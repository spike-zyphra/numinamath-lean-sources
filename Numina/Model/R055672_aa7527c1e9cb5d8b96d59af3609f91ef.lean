import Mathlib

theorem number_theory_115031 {n : ℕ} (hn : n = 7744) :
    ∃ k, n = k^2 ∧ (n / 100) % 11 = 0 ∧ n % 11 = 0 := by
  use 88
  rw [hn]
  repeat {constructor}
  all_goals norm_num