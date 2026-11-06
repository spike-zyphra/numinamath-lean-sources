import Mathlib

open Real

theorem inequalities_599406 (a : ℕ → ℝ) (ha1 : a 1 = 1)
    (han : ∀ n, a (n + 1) = a n / n + n / a n) (n : ℕ) (hn : 4 ≤ n) :
    sqrt n < a n ∧ a n < sqrt (n + 1) := by
  have h1 := han 0
  norm_num [ha1] at h1
  all_goals
    linarith