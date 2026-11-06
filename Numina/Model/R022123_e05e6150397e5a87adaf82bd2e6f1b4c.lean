import Mathlib

/- If positive numbers $x$, $y$ satisfy $x+3y=5xy$, then the minimum value of $3x+4y$ is ___          ___. -/
theorem algebra_11205 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + 3 * y = 5 * x * y) :
    3 * x + 4 * y ≥ 5 := by
  have h1 : x * y > 0 := mul_pos hx hy
  have h2 : 3 / x + 1 / y = 5 := by
    have hx_ne_zero : x ≠ 0 := ne_of_gt hx
    have hy_ne_zero : y ≠ 0 := ne_of_gt hy
    field_simp [hx_ne_zero, hy_ne_zero]
    linarith
  have hx_ne_zero : x ≠ 0 := ne_of_gt hx
  have hy_ne_zero : y ≠ 0 := ne_of_gt hy
  have h3 : (3 * x + 4 * y) * (3 / x + 1 / y) ≥ 25 := by
    have h4 : (3 * x + 4 * y) * (3 / x + 1 / y) = 13 + 3 * x / y + 12 * y / x := by
      field_simp [hx_ne_zero, hy_ne_zero]
      ring
    rw [h4] at *
    have h5 : 3 * x / y + 12 * y / x ≥ 12 := by
      have h6 : 3 * x / y + 12 * y / x - 12 ≥ 0 := by
        have h7 : 3 * x / y + 12 * y / x - 12 = (3 * (x ^ 2) + 12 * (y ^ 2) - 12 * (x * y)) / (x * y) := by
          field_simp [hx_ne_zero, hy_ne_zero]
          ring
        rw [h7] at *
        have h8 : 3 * (x ^ 2) + 12 * (y ^ 2) - 12 * (x * y) ≥ 0 := by
          nlinarith [sq_nonneg (x - 2 * y)]
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith
  have h9 : (3 / x + 1 / y) = 5 := h2
  have h10 : (3 * x + 4 * y) * 5 ≥ 25 := by
    have h11 : (3 / x + 1 / y) = 5 := h9
    have h12 : (3 * x + 4 * y) * (3 / x + 1 / y) = (3 * x + 4 * y) * 5 := by
      rw [h11]
    nlinarith [h3, h12]
  linarith