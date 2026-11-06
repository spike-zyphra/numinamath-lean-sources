import Mathlib

theorem algebra_314716 {a b c d : ℝ} (h1 : a ≥ b ∧ b ≥ c ∧ c ≥ d)
    (h2 : a + b + c + d = 9) (h3 : a^2 + b^2 + c^2 + d^2 = 21) :
    a + b ≥ 5 ∧ a * b - c * d ≥ 2 := by
  have h4 : a ≥ b := h1.1
  have h5 : b ≥ c := h1.2.1
  have h6 : c ≥ d := h1.2.2
  have h7 : a + b ≥ 5 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b - c - d), sq_nonneg (b - c)]
  have h8 : a * b - c * d ≥ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b - c - d), sq_nonneg (b - c)]
  constructor
  · linarith
  · linarith