import Mathlib

/- Simplify the expression $$(x^5+3x^2+3x^5)-(x^7+2x^2+6x^5).$$ -/
theorem algebra_22243 (x : ℝ) :
    (x^5 + 3 * x^2 + 3 * x^5) - (x^7 + 2 * x^2 + 6 * x^5) = -x^7 - 2 * x^5 + x^2 := by
        ring_nf
