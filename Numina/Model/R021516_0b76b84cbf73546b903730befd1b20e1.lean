import Mathlib

theorem algebra_38234 (n : ℕ) (hn : n > 0) (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : x * y = n * x + n * y) :
    n + 1 ≤ x ∧ x ≤ n * (n + 1) := by
  have h1 : x * y = n * x + n * y := h
  have h2 : x ≤ n * (n + 1) := by
    by_cases h3 : y ≤ n
    · -- Assume y ≤ n
      nlinarith [sq_nonneg (x - n), sq_nonneg (y - n), sq_nonneg (n - 1), mul_pos hx hy, mul_pos (show 0 < n by linarith) hx, mul_pos (show 0 < n by linarith) hy]
    · -- Assume y > n
      have h4 : x ≤ n * (n + 1) := by
        nlinarith [sq_nonneg (x - n * (n + 1)), sq_nonneg (y - n - 1), sq_nonneg (n - 1), mul_pos hx hy, mul_pos (show 0 < n by linarith) hx, mul_pos (show 0 < n by linarith) hy]
      linarith
  have h3 : n + 1 ≤ x := by
    by_cases h4 : x ≤ n
    · -- Assume x ≤ n
      nlinarith [sq_nonneg (x - n), sq_nonneg (y - n), sq_nonneg (n - 1), mul_pos hx hy, mul_pos (show 0 < n by linarith) hx, mul_pos (show 0 < n by linarith) hy]
    · -- Assume x > n
      have h5 : n + 1 ≤ x := by
        nlinarith [sq_nonneg (x - n), sq_nonneg (y - n), sq_nonneg (n - 1), mul_pos hx hy, mul_pos (show 0 < n by linarith) hx, mul_pos (show 0 < n by linarith) hy]
      linarith
  constructor
  · -- Proof of Minimum bound
    linarith [h3]
  · -- Proof of Maximum bound
    linarith [h2]