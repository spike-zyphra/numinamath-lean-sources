import Mathlib

theorem algebra_302355 (a : ℝ) (h : ∃ x1 x2, x1^2 + (a^2 - 9)*x1 + a^2 - 5*a + 6 = 0 ∧
    x2^2 + (a^2 - 9)*x2 + a^2 - 5*a + 6 = 0 ∧ x1 < 0 ∧ x2 > 2) :
    2 < a ∧ a < 8 / 3 := by 
  rcases h with ⟨x1, x2, h1, h2, h3, h4⟩
  have h5 : a^2 - 5 * a + 6 < 0 := by
    nlinarith [sq_nonneg (x1 - 0), sq_nonneg (x1), sq_nonneg (x2), sq_nonneg (x2 - 2)]
  have h51 : 2 < a := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (a - 3)]
  have h52 : a < 8 / 3 := by 
    nlinarith [sq_nonneg (x2 - 2), sq_nonneg (a - 2), sq_nonneg (a - 8 / 3), sq_nonneg (x2 * 2)]
  constructor
  · nlinarith
  · nlinarith