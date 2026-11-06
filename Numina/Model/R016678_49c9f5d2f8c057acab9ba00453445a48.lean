import Mathlib

theorem algebra_316627 :
    ∀ N : ℕ, ∃ m n : ℕ,
      m > N ∧ n > N ∧ m^2 + 25 * n^2 = 10 * m * n + 7 * (m + n) := by
  intro N
  use 840 * N ^ 2 + 434 * N + 56, 168 * N ^ 2 + 70 * N + 7
  constructor
  · -- Show m > N
    nlinarith [sq_nonneg (N : ℕ), sq_nonneg (N + 1 : ℕ)]
  constructor
  · -- Show n > N
    nlinarith [sq_nonneg (N : ℕ), sq_nonneg (N + 1 : ℕ)]
  · -- Show m^2 + 25 * n^2 = 10 * m * n + 7 * (m + n)
    ring