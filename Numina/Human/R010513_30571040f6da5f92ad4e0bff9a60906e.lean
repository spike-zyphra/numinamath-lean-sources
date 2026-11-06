import Mathlib

/--
Twenty percent less than 60 is one-third more than what number?
$\mathrm{(A)}\ 16\qquad \mathrm{(B)}\ 30\qquad \mathrm{(C)}\ 32\qquad \mathrm{(D)}\ 36\qquad \mathrm{(E)}\ 48$
-/
theorem algebra_1209 {x : ℝ} (hx : 60 - 60 * 0.2 = x + x / 3) : x = 36 := by
  -- Express the condition as an equation involving a variable $x$ and then solve for $x$ with basic algebra.
  linarith