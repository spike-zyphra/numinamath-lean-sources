import Mathlib

theorem algebra_311413 (x : ℝ) (hx : x ≠ 0) : 1 / x - 2 = x ^ 2 - 2 * x ↔ x = 1 := by
  constructor
  · -- Assume the equation $\frac{1}{x}-2 = x^2 - 2x$, prove $x = 1$
    intro h
    have h1 : x ≠ 0 := hx
    field_simp at h
    have h2 : x ^ 3 - 2 * x ^ 2 + 2 * x - 1 = 0 := by
      nlinarith [sq_nonneg (x), sq_pos_of_ne_zero hx]
    have h3 : (x - 1) * (x ^ 2 - x + 1) = 0 := by
      linarith [h2]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case where $x - 1 = 0$, so $x = 1$
      linarith
    · -- Case where $x^2 - x + 1 = 0$
      have h6 : x ^ 2 - x + 1 > 0 := by
        nlinarith [sq_nonneg (x - 1 / 2)]
      have h5' : x ^ 2 - x + 1 = 0 := by
        linarith [sq_nonneg (x), sq_pos_of_ne_zero hx, h5]
      linarith [h6, h5']
  · -- Assume $x = 1$, prove $\frac{1}{x}-2 = x^2 - 2x$
    intro h
    rw [h]
    norm_num