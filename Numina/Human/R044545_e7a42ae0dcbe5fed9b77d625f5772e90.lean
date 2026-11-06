import Mathlib

open Real

theorem algebra_327323 : logb 27 124 < 3 / 2 ∧ 3 / 2 < logb 16 82 := by
  constructor
  . cancel_denoms
    rw [← logb_rpow_eq_mul_logb_of_pos (by simp), Real.logb_lt_iff_lt_rpow (by simp) (by simp)]
    norm_num
  . cancel_denoms
    rw [← logb_rpow_eq_mul_logb_of_pos (by simp), Real.lt_logb_iff_rpow_lt (by simp) (by simp)]
    norm_num
