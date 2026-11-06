import Mathlib

theorem inequalities_82412 (x : ℝ) (hx : x ≠ 0) :
    x ^ 8 - x ^ 5 - 1 / x + 1 / x ^ 4 ≥ 0 := by 
  have h1 : x^4 > 0 := by
    have h2 : x^2 > 0 := sq_pos_of_ne_zero hx
    positivity 
  have h2 : x^8 - x^5 - 1 / x + 1 / x^4 = (x^12 - x^9 - x^3 + 1) / x^4 := by 
    field_simp [hx]
    <;> ring 
  have h3 : (x^12 - x^9 - x^3 + 1) ≥ 0 := by 
    nlinarith [sq_nonneg (x^3 - 1), sq_nonneg (x^6), sq_nonneg (x^3 + x^0), sq_nonneg (x - 1), sq_nonneg (x^3 + 1 / 2), sq_nonneg (x^3 * x^3 + 1 / 2), sq_nonneg (x^3), sq_nonneg (x^3 - 1), sq_nonneg (x^3 + 1), sq_nonneg (x^2), sq_nonneg (x^2 - x), sq_nonneg (x^2 + 1)]
  rw [h2] 
  apply div_nonneg 
  linarith
  positivity