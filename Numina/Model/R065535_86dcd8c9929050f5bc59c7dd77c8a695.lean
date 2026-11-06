import Mathlib

theorem algebra_215957 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) :
    -1/2 ≤ a*b + b*c + a*c ∧ a*b + b*c + a*c ≤ 1 := by
  have h1 : -1/2 ≤ a * b + b * c + a * c := by
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h2 : a * b + b * c + a * c ≤ 1 := by
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  exact ⟨h1, h2⟩