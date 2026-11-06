import Mathlib

open Real
open scoped BigOperators

theorem inequalities_43976 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0)
  (h₂ : c > 0) (h₃ : a^2 + b^2 = c^2) :
  3 * a + 4 * b ≤ 5 * c := by 
  nlinarith [sq_nonneg (4 * a - 3 * b), sq_nonneg (c - ( (3 * a + 4 * b) / 5)), sq_nonneg (a * 4 - b * 3), sq_nonneg (a - b), sq_nonneg (c - a), sq_nonneg (c - b),
    sq_nonneg (c - a - b), sq_nonneg (c - 5), sq_nonneg (a - 3), sq_nonneg (b - 4)]