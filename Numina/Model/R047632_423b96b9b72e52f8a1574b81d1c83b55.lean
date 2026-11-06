import Mathlib

theorem algebra_298754 (a b : ℝ) (h : ∃ x : ℝ, x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 = 0) :
    a ^ 2 + b ^ 2 ≥ 4 / 5 := by
  rcases h with ⟨x, hx⟩
  have h1 : x ≠ 0 := by
    by_contra h1
    rw [h1] at hx
    nlinarith
  have h2 : a ^ 2 + b ^ 2 ≥ 4 / 5 := by
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x * (x + 1) ), sq_nonneg (x * (x - 1) ), sq_nonneg (x ^ 2 - 1 / x ^ 2), sq_nonneg (x + 1 / x), sq_nonneg (x * (x + 1 / x) - 2), sq_nonneg ((x + 1 / x) ^ 2 - 4), sq_nonneg ((x^2 - 1) / x), sq_nonneg (x * 1 / x - 1), sq_nonneg ((x + 1 / x) * x - 2), sq_nonneg (a + 4 / 5), sq_nonneg (b + 2 / 5), sq_nonneg (a - 4 / 5), sq_nonneg (b + 2 / 5), sq_nonneg (b - (-2 / 5)), sq_nonneg (a - (4 / 5) ) ]
  linarith [h2]