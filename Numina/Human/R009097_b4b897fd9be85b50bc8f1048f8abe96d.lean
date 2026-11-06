import Mathlib

/- What is the value of
(625^(log_⁡5(⁡2015))^(1/4)?
(A) 5
(B) (2015)^(1/4)
(C) 625
(D) 2015
(E) 5^(2015)^(1/4) -/

theorem algebra_96904 : (625 : ℝ) ^ ((Real.logb 5 2015) / 4) = 2015 := by
  -- we just calculate
  calc 625 ^ (Real.logb 5 2015 / 4)
  _ = ((5:ℝ)^(4:ℝ)) ^ (Real.logb 5 2015 / 4) := by norm_num
  _ = 5 ^ (4 * (Real.logb 5 2015 / 4)) := by rw [← Real.rpow_mul (by norm_num)]
  _ = 5 ^ Real.logb 5 2015 := by ring_nf
  _ = 2015 := by rw [Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]