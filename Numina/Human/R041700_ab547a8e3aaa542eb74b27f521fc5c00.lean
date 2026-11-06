import Mathlib

open Complex

/- Evaluate $i^{11} + i^{16} + i^{21} + i^{26} + i^{31}$. -/
theorem algebra_10333 : I^11 + I^16 + I^21 + I^26 + I^31 = -I := by
  apply Complex.ext
  . norm_num [pow_succ]
  . norm_num [pow_succ]
