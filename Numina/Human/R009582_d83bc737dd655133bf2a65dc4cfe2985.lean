import Mathlib

/- Write $\sqrt{\frac{16}{25}+\frac{9}{4}}$ as a common fraction. -/
theorem algebra_10973 : Real.sqrt ((16/25) + (9/4)) = 17/10 := by
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num