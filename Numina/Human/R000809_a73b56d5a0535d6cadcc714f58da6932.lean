import Mathlib

/- What is the greatest common divisor of $2^{1998}-1$ and $2^{1989}-1$? -/
theorem number_theory_16239 : gcd (2^1998 - 1) (2^1989 - 1) = 511 := by
  norm_num;
  decide