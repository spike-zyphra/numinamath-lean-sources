import Mathlib

theorem algebra_294910 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (3 * x + y)^5 + x^5 + 4 * x + y = 0) : x / y = -1 / 4 := by
  have eq1 : (3 * x + y) ^ 5 + (3 * x + y) + x ^ 5 + x = 0 := by
    nlinarith
  have eq2 : (3 * x + y + x) * ((3 * x + y)^4 - (3 * x + y)^3 * x + (3 * x + y)^2 * x^2 - (3 * x + y) * x^3 + x^4 + 1) = 0 := by
    ring_nf at eq1 ⊢
    nlinarith
  cases' (mul_eq_zero.mp eq2) with h3 h4
  · -- Case 1: $4x + y = 0$, so $y = -4x$, so $\frac{x}{y} = -\frac{1}{4}$.
    have hy1 : y = -4 * x := by
      linarith
    have hxy : x / y = -1 / 4 := by
      rw [show y = -4 * x by linarith [hy1]]
      field_simp [hx, show -4 * x ≠ 0 by
        intro h0
        apply hx
        linarith
      ]
      <;> nlinarith
    exact hxy
  · -- Case 2: The second factor is zero.
    nlinarith [sq_nonneg ((3 * x + y)^2 + x^2), sq_nonneg ((3 * x + y) - x), sq_nonneg ((3 * x + y) + x), sq_nonneg ((3 * x + y)^3 - x^3), sq_nonneg ((3 * x + y) * x), sq_nonneg ((3 * x + y)^2 - x^2), sq_nonneg ((3 * x + y) * x * (3 * x + y + x)), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_nonneg ( (3 * x + y) * x ) ]