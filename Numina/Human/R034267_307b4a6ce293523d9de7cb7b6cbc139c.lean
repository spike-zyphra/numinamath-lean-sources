import Mathlib

open Real

/- 1. $\arcsin (\sin \sqrt{3})-\arcsin (\cos 5)=$ -/
theorem algebra_230873 : arcsin (sin (sqrt 3)) - arcsin (cos 5) = (5 * π / 2) - 5 - sqrt 3 := by
  -- We have sin √3 = sin (π - √3).
  -- -π / 2 < π - √3 < π / 2, so arcsin(sin (π - √3)) = π - √3.
  rw [← sin_pi_sub, arcsin_sin]
  rotate_left
  · suffices √3 < 2 by linarith [pi_gt_d2]
    rw [sqrt_lt' (by norm_num)]
    norm_num
  · suffices 1.7 < √3 by linarith [pi_lt_d2]
    rw [lt_sqrt (by norm_num)]
    norm_num
  -- arcsin x = π / 2 - arccos x.
  rw [arcsin_eq_pi_div_two_sub_arccos]
  -- cos 5 = cos (2π - 5).
  -- 0 ≤ 2π - 5 ≤ π, so arccos (cos (2π - 5)) = 2π - 5.
  rw [← cos_two_pi_sub]
  rw [arccos_cos (by linarith [pi_gt_d2]) (by linarith [pi_lt_d2])]
  -- π - √3 - (π / 2 - (2π - 5)) = 5 π / 2 - 5 - √3.
  ring