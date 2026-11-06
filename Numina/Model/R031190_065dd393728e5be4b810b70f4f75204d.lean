import Mathlib

open Real

theorem algebra_169711 {A B : ℝ}
    (hA : A = sqrt 5 + sqrt (22 + 2 * sqrt 5))
    (hB : B = sqrt (11 + 2 * sqrt 29) + sqrt (16 - 2 * sqrt 29 + 2 * sqrt (55 - 10 * sqrt 29))) :
    A = B := by
  have h2 : sqrt (22 + 2 * sqrt 5) = sqrt (11 + 2 * sqrt 29) + sqrt (11 - 2 * sqrt 29) := by
    have h11 : (sqrt (11 + 2 * sqrt 29) + sqrt (11 - 2 * sqrt 29)) ^ 2 = 22 + 2 * sqrt 5 := by
      have h111 : (sqrt (11 + 2 * sqrt 29) : ℝ) ^ 2 = 11 + 2 * sqrt 29 := by
        rw [Real.sq_sqrt]
        nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (29 : ℝ) ≥ 0 by norm_num)]
      have h112 : (sqrt (11 - 2 * sqrt 29) : ℝ) ^ 2 = 11 - 2 * sqrt 29 := by
        rw [Real.sq_sqrt]
        nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (29 : ℝ) ≥ 0 by norm_num)]
      have h113 : (sqrt (11 + 2 * sqrt 29) : ℝ) * (sqrt (11 - 2 * sqrt 29) : ℝ) = sqrt 5 := by 
        have h113'1 : (sqrt (11 + 2 * sqrt 29) : ℝ) * (sqrt (11 - 2 * sqrt 29) : ℝ) = sqrt ((11 + 2 * sqrt 29) * (11 - 2 * sqrt 29)) := by 
          rw [← Real.sqrt_mul (by 
            nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (29 : ℝ) ≥ 0 by norm_num)]
          )]
        have h113'2 : (11 + 2 * sqrt 29) * (11 - 2 * sqrt 29) = (5 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (29 : ℝ) ≥ 0 by norm_num)]
        have h5'1 : sqrt ((11 + 2 * sqrt 29) * (11 - 2 * sqrt 29)) = sqrt (5 : ℝ) := by 
          rw [h113'2]
        rw [h113'1, h5'1]
      nlinarith [Real.sqrt_nonneg (11 + 2 * sqrt 29), Real.sqrt_nonneg (11 - 2 * sqrt 29), Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
    have h12 : sqrt (11 + 2 * sqrt 29) + sqrt (11 - 2 * sqrt 29) ≥ 0 := by positivity
    have h13 : sqrt (22 + 2 * sqrt 5) = sqrt ((sqrt (11 + 2 * sqrt 29) + sqrt (11 - 2 * sqrt 29)) ^ 2) := by
      rw [h11]
    rw [h13, Real.sqrt_sq (by positivity)]
  have h3 : sqrt (16 - 2 * sqrt 29 + 2 * sqrt (55 - 10 * sqrt 29)) = sqrt 5 + sqrt (11 - 2 * sqrt 29) := by
    have h14 : (sqrt 5 + sqrt (11 - 2 * sqrt 29)) ^ 2 = 16 - 2 * sqrt 29 + 2 * sqrt (55 - 10 * sqrt 29) := by 
      have h111 : (sqrt (11 - 2 * sqrt 29) : ℝ) ^ 2 = 11 - 2 * sqrt 29 := by
        rw [Real.sq_sqrt]
        nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (29 : ℝ) ≥ 0 by norm_num)]
      have h144 : (sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)
      have h113 : (sqrt 5 : ℝ) * (sqrt (11 - 2 * sqrt 29) : ℝ) = sqrt (55 - 10 * sqrt 29) := by 
        have h113_1 : (sqrt 5 : ℝ) * (sqrt (11 - 2 * sqrt 29) : ℝ) = sqrt (5 * (11 - 2 * sqrt 29)) := by 
          rw [← Real.sqrt_mul (by 
            nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (29 : ℝ) ≥ 0 by norm_num)]
          )]
        have h113_2 : 5 * (11 - 2 * sqrt 29) = (55 - 10 * sqrt 29 : ℝ) := by 
          ring
        rw [h113_1, h113_2]
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg (11 - 2 * sqrt 29), Real.sqrt_nonneg (55 - 10 * sqrt 29), Real.sq_sqrt (show (55 - 10 * sqrt 29) ≥ 0 by nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (29 : ℝ) ≥ 0 by norm_num)]), Real.sq_sqrt (show (5 * (11 - 2 * sqrt 29)) ≥ 0 by nlinarith [Real.sqrt_nonneg 29, Real.sq_sqrt (show (29 : ℝ) ≥ 0 by norm_num)])]
    have h15 : sqrt 5 + sqrt (11 - 2 * sqrt 29) ≥ 0 := by positivity
    have h16 : sqrt (16 - 2 * sqrt 29 + 2 * sqrt (55 - 10 * sqrt 29)) = sqrt ((sqrt 5 + sqrt (11 - 2 * sqrt 29))  ^ 2) := by 
      rw [h14]
    rw [h16, Real.sqrt_sq (by positivity)]
  rw [hA, hB]
  rw [h2, h3]
  all_goals nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg (11 + 2 * sqrt 29), Real.sqrt_nonneg (11 - 2 * sqrt 29)]