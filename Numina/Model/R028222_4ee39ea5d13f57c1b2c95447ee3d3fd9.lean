import Mathlib

theorem algebra_222841 (n : ℤ) :
    ∃ m, m^2 = n^4 + 6 * n^3 + 11 * n^2 + 3 * n + 31 ↔ n = 10 := by
  use 131
  constructor
  · -- Forward: if 131^2 = ..., then n = 10
    intro h
    have h1 : n ^ 4 + 6 * n ^ 3 + 11 * n ^ 2 + 3 * n + 31 = 17161 := by
      nlinarith
    have h3 : n ≤ 20 := by
      nlinarith [sq_nonneg (n ^ 2 + 3 * n + 1 - 131), sq_nonneg (n ^ 2 + 3 * n + 1 + 131), sq_nonneg (n - 10), sq_nonneg (n + 10), sq_nonneg (n ^ 2 - 100), sq_nonneg ((n + 10) ^ 2), sq_nonneg ((n - 20) * (n - 20))]
    have h4 : n ≥ -20 := by
      nlinarith [sq_nonneg (n ^ 2 + 3 * n + 1 - 131), sq_nonneg (n ^ 2 + 3 * n + 1 + 131), sq_nonneg (n - 10), sq_nonneg (n + 10), sq_nonneg (n ^ 2 - 100), sq_nonneg ((n + 10) ^ 2), sq_nonneg ((n + 20) * (n + 20))]
    interval_cases n <;> omega
  · -- Backward: if n = 10, then 131^2 = ...
    intro h
    rw [h]
    norm_num