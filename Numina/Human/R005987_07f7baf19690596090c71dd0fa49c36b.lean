import Mathlib
/- Real numbers $a, b, c$ satisfy the equations $a+b+c=26,1 / a+1 / b+1 / c=28$. Find the value of

$$
\frac{a}{b}+\frac{b}{c}+\frac{c}{a}+\frac{a}{c}+\frac{c}{b}+\frac{b}{a} .
$$ -/
theorem algebra_610972 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h : a + b + c = 26) (h2 : 1 / a + 1 / b + 1 / c = 28) : a / b + b / c + c / a + a / c + c / b + b / a = 725:= by
  -- Key insight: The target expression plus 3 equals the product of the sums (26 * 28)
  suffices a / b + b / c + c / a + a / c + c / b + b / a + 3 = 26 * 28 by linarith
  -- Use the given equations
  rw [←h, ←h2]
  -- Simplify fractions
  field_simp
  -- Complete the proof using linear arithmetic
  linarith
