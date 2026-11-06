import Mathlib

theorem algebra_254998 (x : ℝ) (hx : x > 0) :
    2 * x + 18 / x ≥ 12 ∧ (∃ x, x > 0 ∧ 2 * x + 18 / x = 12) := by
  constructor
  · -- First part: Show that $2x + \frac{18}{x} \geq 12$ for any positive real number $x$
    have h1 : 2 * x + 18 / x - 12 ≥ 0 := by
      have h2 : x > 0 := hx
      have h3 : 2 * x + 18 / x - 12 = (2 * x ^ 2 + 18 - 12 * x) / x := by
        field_simp
        ring
      rw [h3]
      apply div_nonneg
      · -- Show that the quadratic expression is non-negative
        nlinarith [sq_nonneg (x - 3)]
      · -- Show that the denominator is non-negative
        linarith
    linarith
  · -- Second part: Show that there exists a positive real number $x$ such that $2x + \frac{18}{x} = 12$
    use 3
    constructor
    · -- Show that 3 is positive
      norm_num
    · -- Show that $2 * 3 + 18 / 3 = 12$
      norm_num