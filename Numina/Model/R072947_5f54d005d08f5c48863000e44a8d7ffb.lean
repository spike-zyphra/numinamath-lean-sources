import Mathlib
open Real

theorem algebra_92949 (e n R r C : ℝ) (he : 0 < e) (hn : 0 < n) (hR : 0 < R) (hr : 0 < r)
(hC : C = e * n / (R + n * r)) (hC1 : C1 = e * (n + 1) / (R + (n + 1) * r)) :
C < C1 := by
  rw [hC, hC1]
  have pos1 : 0 < R + n * r := by
    positivity
  have pos2 : 0 < R + (n + 1) * r := by
    positivity
  apply (div_lt_div_iff (by positivity) (by positivity)).mpr
  suffices e * n * (R + (n + 1) * r) < e * (n + 1) * (R + n * r) by
    linarith
  -- e * n * (R + (n + 1) * r) < e * (n + 1) * (R + n * r)
  nlinarith [mul_pos he hn, mul_pos he hR, mul_pos he hr, mul_pos hn hR, mul_pos hn hr, mul_pos hR hr]