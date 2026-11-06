import Mathlib
/- Let $a$ and $b$ be positive integers. Let $M = (a+b)^2$. Prove that the number $a^2 b^2 + (a^2+b^2)M$ is the square of an integer. Show that this integer is $a^2+b^2+ab$. -/
theorem algebra_635493 (a b M : ℤ) (ha : a > 0) (hb : b > 0) (hM : M = (a + b) ^ 2) : a ^ 2 * b ^ 2 + (a ^ 2 + b ^ 2) * M = (a ^ 2 + b ^ 2 + a * b) ^ 2:= by
  -- Substitute M with (a + b) ^ 2
  subst M
  -- Expand the expression
  linarith
