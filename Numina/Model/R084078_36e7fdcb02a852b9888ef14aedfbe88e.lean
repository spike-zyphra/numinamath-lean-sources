import Mathlib

theorem algebra_78746 (p q r : ℝ) (h : p ≠ q ∧ q ≠ r ∧ r ≠ p)
    (h1 : p^3 - p^2 + p - 2 = 0) (h2 : q^3 - q^2 + q - 2 = 0)
    (h3 : r^3 - r^2 + r - 2 = 0) :
    p^3 + q^3 + r^3 = -6 := by
  have h7 : p - q ≠ 0 := sub_ne_zero_of_ne h.1
  have eq1 : (p - q) * (p^2 + p * q + q^2 - (p + q) + 1) = 0 := by
    ring_nf
    nlinarith [h1, h2]
  cases (mul_eq_zero.mp eq1) with
  | inl h8 =>
    exfalso
    exact h.1 (by linarith)
  | inr h9 =>
    nlinarith [sq_nonneg (p - q), sq_nonneg (p + q - 1), sq_nonneg (p - 1), sq_nonneg (q - 1)]