import Mathlib

theorem algebra_1613 {a b c : ℝ} (ha : a = 19951995 / 19961996) (hb : b = 19961996 / 19971997)
    (hc : c = 19971997 / 19981998) : a < b ∧ b < c := by
  rw [ha, hb, hc]
  constructor
  · -- Prove that $\frac{19951995}{19961996} < \frac{19961996}{19971997}$
    norm_num
  · -- Prove that $\frac{19961996}{19971997} < \frac{19971997}{19981998}$
    norm_num