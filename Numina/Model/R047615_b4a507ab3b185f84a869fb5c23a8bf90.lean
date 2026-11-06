import Mathlib

theorem algebra_221896 (a : ℝ) (h : ∃ x y, x^2 + 4 * (y - a)^2 = 4 ∧ x^2 = 2 * y) :
    a ∈ Set.Icc (-1) (17 / 8) := by
  rcases h with ⟨x, y, h1, h2⟩

  have h3 : a ≤ 17 / 8 := by
    nlinarith [sq_nonneg (y + 1 / 4 - a), sq_nonneg (x ^ 2 - 2 * y), sq_nonneg (y - a), sq_nonneg (x ^ 2 - 2 * y)]

  have h4 : a ≥ -1 := by
    nlinarith [sq_nonneg (y + 1 / 4 - a), sq_nonneg (x ^ 2 - 2 * y), sq_nonneg (y - a), sq_nonneg (x ^ 2 - 2 * y)]

  constructor
  · linarith
  · linarith