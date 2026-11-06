import Mathlib

/- Let $a,$ $b,$ and $c$ be distinct real numbers.  Simplify the expression
\[\frac{(x + a)^3}{(a - b)(a - c)} + \frac{(x + b)^3}{(b - a)(b - c)} + \frac{(x + c)^3}{(c - a)(c - b)}.\] -/
theorem algebra_15466 (a b c x : ℝ) (ha : a ≠ b) (hb : a ≠ c) (hc : b ≠ c) :
    ((x + a)^3 / ((a - b) * (a - c)) + (x + b)^3 / ((b - a) * (b - c)) +
     (x + c)^3 / ((c - a) * (c - b))) = a + b + c + 3 * x := by
  field_simp [sub_ne_zero.2 ha, sub_ne_zero.2 hb, sub_ne_zero.2 hc, sub_ne_zero.2 ha.symm,
    sub_ne_zero.2 hb.symm, sub_ne_zero.2 hc.symm]
  ring