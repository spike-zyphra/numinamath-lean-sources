import Mathlib
open Real

theorem geometry_96037
  {a b d : ℝ}
  (ha : a = 1)
  (hb : b = 8)
  (hc : d = 9)
  : √(a^2 + b^2 + 4^2) = d
:= by 
  rw [ha, hb, hc]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> ring_nf <;> norm_num