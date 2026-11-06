import Mathlib

open Real

theorem algebra_134445 (a : ℕ → ℝ) (ha : a 0 = 0)
    (h : ∀ n, a (n + 1) = a n + 1 / (n + 1) - 1 / (n + 2)) :
    a 44 = 44 / 45 := by
  norm_num [ha, h]