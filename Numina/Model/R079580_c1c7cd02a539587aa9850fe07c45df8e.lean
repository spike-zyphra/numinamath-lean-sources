import Mathlib

theorem algebra_9978 {x y : Fin 2 → ℝ} (h1 : x 0 ^ 2 + 5 * x 1 ^ 2 = 10)
    (h2 : x 1 * y 0 - x 0 * y 1 = 5) (h3 : x 0 * y 0 + 5 * x 1 * y 1 = Real.sqrt 105) :
    y 0 ^ 2 + 5 * y 1 ^ 2 = 23 := by
  have h2_sqr : (x 1 * y 0 - x 0 * y 1) ^ 2 = 25 := by
    rw [h2]
    norm_num
  have h3_sqr : (x 0 * y 0 + 5 * x 1 * y 1) ^ 2 = 105 := by
    calc
      (x 0 * y 0 + 5 * x 1 * y 1) ^ 2 = (Real.sqrt 105) ^ 2 := by
        rw [h3]
      _ = 105 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
  nlinarith [sq_nonneg (x 0 * x 1), sq_nonneg (x 0 * y 1 - x 1 * y 0), sq_nonneg (x 0 * y 0 + x 1 * y 1), sq_nonneg (x 1), sq_nonneg ((x 0 * y 0 + x 1 * y 1) / (Real.sqrt 105 : ℝ)), sq_nonneg ((x 1 * y 1 + x 0 * y 0) / (Real.sqrt 105 : ℝ)), Real.sqrt_nonneg 105, Real.sq_sqrt (show (105 : ℝ) ≥ 0 by norm_num), sq_nonneg (x 0 * y 0 * x 1 * x 1), sq_nonneg (x 0 * y 0 * (x 1 * x 1)), sq_nonneg ((x 0 * x 0 * 5) * (y 0 * y 0)), sq_nonneg ((x 0 * y 0) * (x 0 * y 0)), sq_nonneg ((x 1 * x 1) * (y 0 * y 0)), sq_nonneg ((x 0 * x 1) * (y 1 * y 1)), sq_nonneg (x 1 * y 1)]