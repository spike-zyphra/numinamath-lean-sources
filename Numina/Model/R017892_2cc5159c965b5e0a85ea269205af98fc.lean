import Mathlib

theorem algebra_4584 {n : ℕ} (hn : n > 0) (h : (n / 2) * 50 + (n / 2) * 60 + 70 = 50 * n) :
    (n / 2) * 40 + (n / 2) * 70 + 70 = 50 * n + 10 * (n / 2) + 10 * (n / 2) + 10 := by
  omega