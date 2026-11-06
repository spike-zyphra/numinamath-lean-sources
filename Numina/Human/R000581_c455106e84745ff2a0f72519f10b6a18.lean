import Mathlib

/- Let $a,$ $b,$ and $c$ be nonzero real numbers, and let
\[x = \frac{b}{c} + \frac{c}{b}, \quad y = \frac{a}{c} + \frac{c}{a}, \quad z = \frac{a}{b} + \frac{b}{a}.\]Simplify $x^2 + y^2 + z^2 - xyz.$ -/
theorem algebra_12890 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (x y z : ℝ) (hx : x = b / c + c / b) (hy : y = a / c + c / a)
    (hz : z = a / b + b / a) :
    x ^ 2 + y ^ 2 + z ^ 2 - x * y * z = 4 := by
  field_simp [ha, hb, hc, hx, hy, hz]
  ring