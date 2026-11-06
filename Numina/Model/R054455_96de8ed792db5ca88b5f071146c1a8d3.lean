import Mathlib

theorem algebra_159596 (n : ℤ) :
    n^5 - 2 * n^4 - 7 * n^2 - 7 * n + 3 = 0 ↔ n = -1 ∨ n = 3 := by
  constructor
  · -- Forward implication: if the equation holds then n ∈ {-1, 3}
    intro h
    have h1 : n^5 - 2 * n^4 - 7 * n^2 - 7 * n + 3 = 0 := h
    have h2 : (n + 1) * (n - 3) * (n^3 + 3 * n - 1) = 0 := by
      nlinarith [sq_nonneg (n^2 * (n^2)), sq_nonneg ((n + 1) * (n - 3)), sq_nonneg (n * (n^2)), sq_nonneg ((n - 3) * (n^3)), sq_nonneg ((n + 1) * (n^3)), sq_nonneg ((n + 1) * (n - 3)), sq_nonneg (n - 3), sq_nonneg (n + 1), sq_nonneg (n^3 + 3 * n - 1), sq_nonneg (n^3), sq_nonneg (n^2 * 3), sq_nonneg (n * 3)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    · -- Case $n + 1 = 0$, so $n = -1$
      left
      omega
    · -- Case $n - 3 = 0$, so $n = 3$
      right
      omega
    · -- Case $n^3 + 3 * n - 1 = 0$
      have h8 : n^3 + 3 * n - 1 = 0 := h4
      have h9 : n ≥ -2 := by
        nlinarith [sq_nonneg (n + 1), sq_nonneg (n - 1), sq_nonneg (n^2 + 1), sq_nonneg (n^2 - 1), sq_nonneg (n^3 + 1), sq_nonneg (n^3 - 1), sq_nonneg (n * (n + 1)), sq_nonneg ((n + 1) * (n - 1)), sq_nonneg (n * (n - 3)), sq_nonneg ((n - 3) * (n + 1))]
      have h10 : n ≤ 1 := by
        nlinarith [sq_nonneg (n + 1), sq_nonneg (n - 1), sq_nonneg (n^2 + 1), sq_nonneg (n^2 - 1), sq_nonneg (n^3 + 1), sq_nonneg (n^3 - 1), sq_nonneg (n * (n + 1)), sq_nonneg ((n + 1) * (n - 1)), sq_nonneg (n * (n - 3)), sq_nonneg ((n - 3) * (n + 1))]
      interval_cases n <;> omega
  · -- Backward implication: n = -1 or n = 3 satisfy the equation
    rintro (hn | hn)
    · -- n = -1
      rw [hn]
      norm_num
    · -- n = 3
      rw [hn]
      norm_num