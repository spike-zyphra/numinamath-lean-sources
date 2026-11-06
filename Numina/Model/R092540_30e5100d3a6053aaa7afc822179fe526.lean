import Mathlib

theorem algebra_200680 (x : ℝ) : (x + 2)^5 + x^5 + 2 * x + 2 = 0 ↔ x = -1 := by
  constructor
  · -- Forward: If $(x + 2)^5 + x^5 + 2 * x + 2 = 0$, then $x = -1$
    intro h
    have h1 : (x + 1) * (2 * x^4 + 8 * x^3 + 32 * x^2 + 48 * x + 34) = 0 := by 
      ring_nf
      nlinarith [h]
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case where $x + 1 = 0$, so $x = -1$
      linarith
    · -- Case where $2 * x^4 + 8 * x^3 + 32 * x^2 + 48 * x + 34 = 0$
      nlinarith [sq_nonneg (x ^ 2 + 2 * x), sq_nonneg (x + 1), sq_nonneg (x * (x + 4)), sq_nonneg ((x + 4) * (x + 4)), sq_nonneg ((x + 1) * (x + 4)), sq_nonneg ((x + 1) * (x + 2)), sq_nonneg ((x + 2) * (x + 4)), sq_nonneg ((2 * x + 1) * (2 * x + 1))]
  · -- Backward: If x = -1, then $(x + 2)^5 + x^5 + 2 * x + 2 = 0$
    intro h
    rw [h]
    norm_num