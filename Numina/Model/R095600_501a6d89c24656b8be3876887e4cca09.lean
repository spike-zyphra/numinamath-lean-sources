import Mathlib

theorem algebra_280454 {n : ℕ} (hn : n > 0) (h : n = (n + 5) * k) (hk : k > 0)
    (h' : n = k * (k + 4)) :
    k = 24 := by
  nlinarith [sq_nonneg (k : ℕ), sq_nonneg (n : ℕ)]