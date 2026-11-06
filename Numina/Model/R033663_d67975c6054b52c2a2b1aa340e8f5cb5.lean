import Mathlib

theorem algebra_284725 (a : ℕ → ℕ) (ha : ∀ n, a n = n ^ 2 + (n - 1) ^ 2 / 2)
    (h : ∀ n, n ≥ 1 ∧ n ≤ 2022) :
    a 1011 = 10231311025154 := by

  have h1 := h 0

  omega