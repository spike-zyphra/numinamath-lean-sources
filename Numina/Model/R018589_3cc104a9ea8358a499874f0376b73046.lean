import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_314321 (n : ℝ) :
  (∀ x : ℝ, n * x^2 + (n - x) * x + n - 1 < 0) ↔ n < 2 / 3 := by
  constructor
  · -- Forward: if ∀x, n *x ^ 2+ (n -x)x +n -1 <0 then n < 2/3
    intro h
    have h1 := h 1
    nlinarith
  · -- Backward: If n < 2/3, then ∀x, n *x^2 + (n -x)x +n -1 <0
    intro hn x
    have h1 : n * x^2 + (n - x) * x + n - 1 = (n - 1) * x ^ 2 + n * x + (n - 1) := by ring
    rw [h1]
    have h2 : n < 2 / 3 := hn
    have h3 : n - 1 < 0 := by linarith
    have h4 : n < 2 / 3 := h2
    have h5 : (n) ^ 2 - 4 * (n - 1) ^ 2 < 0 := by
      nlinarith
    nlinarith [ sq_nonneg (x + n / (2 * (n - 1))), sq_nonneg (x - 1), sq_nonneg (x - 1/3), sq_nonneg (x - 2), 
          sq_nonneg (n), sq_nonneg (n - 1), sq_nonneg (x + 1), sq_nonneg (x - 2/3),
          sq_nonneg (x + 2/3), sq_nonneg (n - 2/3), mul_self_nonneg (n - 2/3), 
          sq_nonneg ((n - 1) * x + n / 2)
    ]