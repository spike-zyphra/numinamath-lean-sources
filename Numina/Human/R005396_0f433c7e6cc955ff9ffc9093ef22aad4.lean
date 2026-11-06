import Mathlib
/- Three real numbers $x, y$, and $z$ are such that $(x+4) / 2=(y+9) /(z-3)=(x+5) /(z-5)$. Determine the value of $x / y$. -/
theorem algebra_608134 (x y z : ℝ) (h1 : (x + 4) / 2 = (y + 9) / (z - 3)) (h2 : (x + 4) / 2 = (x + 5) / (z - 5)) (hx : x ≠ 0) (hz1 : z - 3 ≠ 0) (hz2 : z - 5 ≠ 0) : x / y = 1 / 2:= by
  -- Let t be the common value of the expressions
  set t:= (x + 4) / 2 with ht
  -- Remove the definition of t from context
  clear_value t
  -- Simplify the field expressions in hypotheses h1 and h2
  field_simp at h1 h2
  -- Prove that y = 2x using linear arithmetic
  have h3 : y = 2 * x:= by linarith
  -- Substitute y with 2x
  subst y
  -- Simplify field expressions
  field_simp
  -- Complete the proof using linear arithmetic
  linarith
