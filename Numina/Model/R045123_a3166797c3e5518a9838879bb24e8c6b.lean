import Mathlib

theorem algebra_307623 {x : ℝ} (hx : x = (Real.sqrt 5 - 1) / 2 - (Real.sqrt 5 - 1) ^ 2 / 4) :
    x ^ ((1 : ℝ) / 3) = (Real.sqrt 5 - 1) / 2 := by
  have h1 : x = Real.sqrt 5 - 2 := by
    rw [hx]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have h2 : x = ((Real.sqrt 5 - 1) / 2) ^ 3 := by
    rw [h1]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have h4 : x ^ ((1 : ℝ) / 3) = (Real.sqrt 5 - 1) / 2 := by
    rw [show x = ((Real.sqrt 5 - 1) / 2) ^ 3 by linarith [h2]]
    have h6 : ( (Real.sqrt 5 - 1) / 2 : ℝ) ≥ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    have h9 : (( ((Real.sqrt 5 - 1) / 2 : ℝ) ) ^ 3 ) ^ ((1 : ℝ) / 3) = (Real.sqrt 5 - 1) / 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    linarith
  exact h4