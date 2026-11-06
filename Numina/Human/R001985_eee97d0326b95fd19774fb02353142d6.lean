import Mathlib

open Real

/-Find (log 2 x)^2 if log 2 (log 8 x)=log 8 (log 2 x).-/
theorem algebra_52320 {x : ℝ} (hx : 1 < x) (h : Real.logb 2 (Real.logb 8 x) = Real.logb 8 (Real.logb 2 x)) :(Real.logb 2 x)^2 = 27 := by
--If all terms are well-defined, then we have 1< x.

--First, we show that we can change the base from 8 to 2.
  have basecha(x:Real) (hx:x>0):logb ((2:ℝ)^(3:ℝ)) x=(logb 2 x)/(logb 2 (2^(3:ℝ))):=by
      simp only [logb]
      field_simp
  have :(8:Real)=2^(3:ℝ):=by norm_cast
  symm at h
--We give an equivalent condition on h.
  have h':logb 2 x = 0 ∨ logb 2 x * logb 2 x - 27 = 0:=by
    rw[logb_eq_iff_rpow_eq] at h
    rw[this,←rpow_mul,mul_comm,rpow_mul,rpow_logb] at h
    rw[basecha x (by linarith)] at h
    rw[logb_rpow] at h
    norm_cast at h
    rw[div_pow,div_eq_iff] at h
    norm_num at h
    all_goals
      try linarith
    norm_cast at h
    rw[pow_three] at h
    rw[←sub_eq_zero] at h
    rw[←mul_sub_left_distrib] at h
    rw[mul_eq_zero] at h
    exact h
    all_goals
      rw[logb_pos_iff]
      linarith
      norm_num
      linarith
--We evaluate log 2 x at each equation.
  rcases h' with h'|h'
  apply eq_one_of_pos_of_logb_eq_zero at h'
  all_goals
  linarith