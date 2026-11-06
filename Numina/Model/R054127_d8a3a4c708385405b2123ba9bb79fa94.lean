import Mathlib

theorem algebra_276568 {x : ℝ} (hx : (5 - 3 * x) ^ 5 = -1) : x = 2 := by
  have h2 : (5 - 3 * x) ^ 5 + 1 = 0 := by linarith
  have h3 : (5 - 3 * x + 1) * ((5 - 3 * x) ^ 4 - (5 - 3 * x) ^ 3 + (5 - 3 * x) ^ 2 - (5 - 3 * x) + 1) = 0 := by
    ring_nf at h2 ⊢
    <;> nlinarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case 1: $5 - 3x + 1 = 0$, which simplifies $x = 2$
    linarith
  · -- Case 2: The polynomial factor is zero
    nlinarith [sq_nonneg ((5 - 3 * x) ^ 2 - (5 - 3 * x) / 2), sq_nonneg ((5 - 3 * x) ^ 2 + (5 - 3 * x) / 2), sq_nonneg ((5 - 3 * x) - 1 / 2), sq_nonneg ((5 - 3 * x) - 1), sq_nonneg ((5 - 3 * x) ), sq_nonneg (5 - 3 * x - 1) ]