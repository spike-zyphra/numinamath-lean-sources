import Mathlib

theorem number_theory_281733 (N : ℕ) (hN : N = 0o12345677654321) :
    N % 7 = 0 ∧ N % 9 = 0 := by
  rw [hN]
  all_goals norm_num