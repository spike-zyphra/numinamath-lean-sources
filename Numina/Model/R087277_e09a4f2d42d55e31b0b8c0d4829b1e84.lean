import Mathlib

theorem algebra_8217 (a b : ℝ) (h : a^2 + a * b + b^2 = 1) :
    a^2 - a * b + b^2 ∈ Set.Icc (1 / 3) 3 := by 
  have h1 : a^2 - a * b + b^2 ≥ 1 / 3 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - b * 2), sq_nonneg (b - a * 2), sq_nonneg (a * 2 + b * 2 - 3 * a * b), sq_nonneg (a - b * 2), sq_nonneg (b - a * 2), sq_nonneg (a + b), sq_nonneg (a - b)]
  have h2 : a^2 - a * b + b^2 ≤ 3 := by 
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a * 2 - b * 2), sq_nonneg (a * b), sq_nonneg (a * 2 + b * 2 - 3 * a * b), sq_nonneg (a * 2 - b * 2), sq_nonneg (a * 2 + b * 2), sq_nonneg (a * b - 1 / 3)]
  exact ⟨h1, h2⟩