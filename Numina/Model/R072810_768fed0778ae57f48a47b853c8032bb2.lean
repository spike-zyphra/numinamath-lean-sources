import Mathlib

theorem algebra_276823 {x : ℝ} (hx : x ≠ -1) (h : x^4 + 4 * x^3 + 6 * x^2 = 3) :
    x^3 + 3 * x^2 + 3 * x + 333 = 336 := by
  have h1 : (x + 1) ^ 4 = 4 * (x + 1) := by
    nlinarith [sq_nonneg (x ^ 2 + 2 * x), sq_nonneg (x + 1)]
  have h2 : (x + 1) * ((x + 1) ^ 3 - 4) = 0 := by
    ring_nf at h1 ⊢
    linarith
  cases (mul_eq_zero.mp h2) with
  | inl h3 =>
    exfalso
    apply hx
    linarith
  | inr h4 =>
    have h5 : (x + 1) ^ 3 = 4 := by linarith
    have h6 : x ^ 3 + 3 * x ^ 2 + 3 * x = (x + 1) ^ 3 - 1 := by
      ring
    linarith [h6, h5]