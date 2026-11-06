import Mathlib

theorem algebra_213457 {n : ℤ} (h : n * (n + 1) * (n + 2) * (n + 3) = 1680) :
    n = 5 ∨ n = -8 := by
  have h1 : n ≤ 8 := by
    by_contra h2
    push_neg at h2
    have h3 : n > 8 := by omega
    have h4 : n * (n + 1) * (n + 2) * (n + 3) ≥ 11880 := by
      have h5 : n ≥ 9 := by omega
      nlinarith [sq_nonneg (n - 9), sq_nonneg (n - 10), sq_nonneg (n - 11), sq_nonneg (n - 12)]
    linarith
  have h2 : n ≥ -9 := by
    by_contra h3
    push_neg at h3
    have h4 : n < -8 := by omega
    have h5 : n * (n + 1) * (n + 2) * (n + 3) ≥ 3024 := by
      nlinarith [sq_nonneg (n + 9), sq_nonneg (n + 8), sq_nonneg (n + 7), sq_nonneg (n + 6)]
    linarith
  interval_cases n <;> omega