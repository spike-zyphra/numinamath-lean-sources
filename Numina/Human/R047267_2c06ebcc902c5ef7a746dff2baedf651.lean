import Mathlib

open Real
open scoped BigOperators

/- A triangle with perimeter $1$ has side lengths $a, b, c$. Show that $a^2 + b^2 + c^2 + 4abc <\frac 12$. -/
theorem inequalities_41999 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (h''' : a + b + c = 1) :
  a^2 + b^2 + c^2 + 4*a*b*c < 1/2 := by 
  -- We use nlinarith tactic with non-negative squares.
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
    -- From $$(b+c-a)^2 \geq 0$$
    mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
    -- Consider from AM-GM achieving kinds of exploitation over AM-遁微量民族 feature.
    mul_pos (sub_pos.mpr h') (sub_pos.mpr h)]