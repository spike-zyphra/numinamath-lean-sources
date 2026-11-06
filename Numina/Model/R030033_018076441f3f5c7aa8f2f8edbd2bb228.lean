import Mathlib

theorem algebra_296632 (x : ℝ) : x^6 - x^3 + 1 = (x^6 + x^3 + 1) * (x^2 + 2 * x + 4) ↔ x = -1 := by
  constructor
  · -- Forward implication: if the equation holds, then x = -1.
    intro h
    have hx1 : x^8 + 2 * x^7 + 3 * x^6 + x^5 + 2 * x^4 + 5 * x^3 + x^2 + 2 * x + 3 = 0 := by
      nlinarith [h]
    have hx2 : (x + 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x ^ 2 + x + 1), sq_nonneg (x + 1), sq_nonneg (x ^ 3 + 1), sq_nonneg (x ^ 2 - x + 1),
          sq_nonneg (x^4 + x^3), sq_nonneg (x^3 * (x + 1)), sq_nonneg ((x + 1)), sq_nonneg (x^4 * (x + 1)), sq_nonneg ((x + 1) * x^2), sq_nonneg ((x^2 + 1)), sq_nonneg (x * (x + 1)), sq_nonneg ((x + 1) * (x^3)), sq_nonneg ((x^2) * (x * (x+1)))]
    -- From $(x + 1)^2 = 0$, we have $x + 1 = 0$. 
    have h3 : x + 1 = 0 := by
      apply pow_eq_zero 
      exact hx2
    linarith
  · -- Backward implication: if x = -1, then the equation holds.
    intro h
    rw [h]
    norm_num