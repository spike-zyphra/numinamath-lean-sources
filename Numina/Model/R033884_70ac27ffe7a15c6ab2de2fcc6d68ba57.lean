import Mathlib

theorem algebra_301821 {x y : ℝ} (hx : x = (1 + Real.sqrt 5) / 2) (hy : y = (1 - Real.sqrt 5) / 2) :
    x^6 + y^6 = 18 := by
  rw [hx, hy]
  have eq1 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 6 + ((1 - Real.sqrt 5) / 2 : ℝ) ^ 6 = 18 := by
    nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num),
          sq_nonneg ( (Real.sqrt 5 : ℝ) ), sq_nonneg ( (Real.sqrt 5) ^ 2 ), sq_nonneg ( (Real.sqrt 5) ^ 4 ), sq_nonneg ( (Real.sqrt 5) ^ 6 ), sq_nonneg ( (1 + Real.sqrt 5) / 2 - (1 - Real.sqrt 5) / 2 ), sq_nonneg ( (1 + Real.sqrt 5) / 2 + (1 - Real.sqrt 5) / 2 ), mul_nonneg (show 0 ≤ Real.sqrt 5 by positivity) (show 0 ≤ Real.sqrt 5 by positivity) ]
  exact_mod_cast eq1