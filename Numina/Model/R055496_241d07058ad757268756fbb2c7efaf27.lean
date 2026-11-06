import Mathlib

theorem algebra_99310 {a b c : ℝ} (h : a^2 + b = b^2 + c ∧ b^2 + c = c^2 + a) :
    a * (a^2 - b^2) + b * (b^2 - c^2) + c * (c^2 - a^2) = 0 := by
  have h1 : a^2 + b = b^2 + c := h.1
  have h2 : b^2 + c = c^2 + a := h.2
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b), sq_nonneg (a - c), sq_nonneg (b - a), sq_nonneg (c - b)]