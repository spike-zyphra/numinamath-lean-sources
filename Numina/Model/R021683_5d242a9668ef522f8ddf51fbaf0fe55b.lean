import Mathlib

open Real

theorem algebra_315698 {x y : ℝ}
    (hx : x = 1 / (sqrt 3 + sqrt 2)) (hy : y = 1 / (sqrt 3 - sqrt 2)) :
    x ^ 2 + y ^ 2 = 10 := by
  have hx2 : x = Real.sqrt 3 - Real.sqrt 2 := by
    rw [hx]
    have h1 : (sqrt 3 + sqrt 2) ≠ 0 := by
      have h2 : sqrt 3 > 0 := by positivity
      have h3 : sqrt 2 > 0 := by positivity
      linarith [show sqrt 2 > 0 from by positivity, show sqrt 3 > 0 from by positivity]
    field_simp [h1]
    <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          sq_nonneg ((sqrt 3) ^ 2 - 2), sq_nonneg ((sqrt 2) ^ 2 - 2)]
  have hy2 : y = Real.sqrt 3 + Real.sqrt 2 := by
    rw [hy]
    have h1 : (sqrt 3 - sqrt 2) ≠ 0 := by
      have h5' : Real.sqrt 3 > Real.sqrt 2 := by
          nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ),
              sq_nonneg ((sqrt 3) ^ 2 - (sqrt 2) ^ 2),
              Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
              Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h4 : Real.sqrt 3 > 0 := by positivity
      have h5 : Real.sqrt 2 > 0 := by positivity
      have h1' : Real.sqrt 3 - Real.sqrt 2 > 0 := by
        nlinarith [h5', Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ),
            sq_nonneg ((sqrt 3) ^ 2 - (sqrt 2) ^ 2),
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
            Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith [h1', h4, h5]
    field_simp [h1]
    <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          sq_nonneg ((sqrt 3) ^ 2 - 2), sq_nonneg ((sqrt 2) ^ 2 - 2)]
  rw [hx2, hy2]
  have h1 : (Real.sqrt (3 : ℝ) : ℝ) ^ 2 = 3 := by
    exact Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt (2 : ℝ) : ℝ) ^ 2 = 2 := by
    exact Real.sq_sqrt (by norm_num)
  nlinarith [h1, h2, Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ),
    sq_nonneg (Real.sqrt 3 * Real.sqrt 2), sq_nonneg (Real.sqrt 3 ^ 2 - 2), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]