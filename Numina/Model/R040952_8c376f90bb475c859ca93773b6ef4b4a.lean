import Mathlib

theorem algebra_7161 {x : ℝ} (hx : x ≠ 0) (h : x^5 + 1/x^5 = 123) :
    x + 1/x = 3 := by
  have h1 : x^5 + 1 / x^5 = (x + 1 / x) ^ 5 - 5 * (x + 1 / x) ^ 3 + 5 * (x + 1 / x) := by
    field_simp
    ring
  rw [h1] at h 
  have h2 : (x + 1 / x) ^ 5 - 5 * (x + 1 / x) ^ 3 + 5 * (x + 1 / x) - 123 = 0 := by 
    linarith 
  have h3 : ((x + 1 / x) ^ 4 + 3 * (x + 1 / x) ^ 3 + 4 * (x + 1 / x) ^ 2 + 12 * (x + 1 / x) + 41) * ((x + 1 / x) - 3) = 0 := by
    nlinarith [sq_nonneg ((x + 1 / x) ^ 2), sq_nonneg ((x + 1 / x) - 3), sq_nonneg ((x + 1 / x) + 3 / 2), sq_nonneg ((x + 1 / x) ^ 2 - 4)]
  cases' (mul_eq_zero.1 h3) with h4 h5 
  · -- Show that ((x + 1 / x) ^ 4 + 3 * (x + 1 / x) ^ 3 + 4 * (x + 1 / x) ^ 2 + 12 * (x + 1 / x) + 41) = 0 has no real solutions
    nlinarith [sq_nonneg ((x + 1 / x) ^ 2), sq_nonneg ((x + 1 / x) + 3 / 2), sq_nonneg ((x + 1 / x) + 2), sq_nonneg ((x + 1 / x) - 2), sq_nonneg ((x + 1 / x) - 5 / 2), sq_nonneg ((x + 1 / x) + 5 / 2)]
  · 
    linarith