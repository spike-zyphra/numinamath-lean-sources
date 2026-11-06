import Mathlib

open Real

/- Without using calculators, tables, etc., prove the inequality $\sin 1 < \log _{3} \sqrt{7}$. -/
theorem inequalities_228653 : sin 1 < logb 3 (sqrt 7) := calc
  -- We have sin 1 < sin(π / 3) because 0 < 1 < π / 3 < π / 2.
  sin 1 < sin (π / 3) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith [pi_lt_d2, pi_gt_d2]
  -- sin(π / 3) = √3 / 2.
  _ = √3 / 2 := by rw [sin_pi_div_three]
  -- √3 / 2 < 7 / 8 because 3 / 4 < 7^2 / 8^2
  _ < 7 / 8 := by
      rw [← sq_lt_sq₀ (by positivity) (by norm_num)]
      rw [div_pow, sq_sqrt (by norm_num)]
      norm_num
  -- Show that 7/8 < logb 3 √7.
  _ < logb 3 √7 := by
      -- We need to show that 3^(7/8) < √7.
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
      -- Raise both sides of the inequality to the 8-th power.
      rw [← pow_lt_pow_iff_left₀ (by positivity) (by positivity) (show 8 ≠ 0 by norm_num)]
      -- We have √7 ^ 8 = 7 ^ 4 = 2401.
      nth_rw 2 [show 8 = 2 * 4 by norm_num]
      rw [pow_mul, sq_sqrt (by norm_num)]
      -- We have 3^(7 / 8)^8 = 3^7 = 2187 < 2401.
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num