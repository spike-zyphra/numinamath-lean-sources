import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_603729 (a b c d e f : ℝ)
  (h₀ : a + b + c + d + e + f = 10)
  (h₁ : (a - 1)^2 + (b - 1)^2 + (c - 1)^2 + (d - 1)^2 + (e - 1)^2 + (f - 1)^2 = 6) :
  f ≤ 10 / 3 := by
  have h2 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2 = 20 := by
    nlinarith
  nlinarith [sq_nonneg (a - 4/3), sq_nonneg (b - 4/3), sq_nonneg (c - 4/3), sq_nonneg (d - 4/3), sq_nonneg (e - 4/3), sq_nonneg (f - 10/3)]