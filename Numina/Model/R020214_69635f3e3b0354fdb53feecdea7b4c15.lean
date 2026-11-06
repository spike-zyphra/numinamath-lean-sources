import Mathlib
open Real

theorem algebra_6334 {a b : ℝ}
    (ha : a = (sqrt 2 + sqrt 3 + sqrt 6) * (sqrt 2 + sqrt 3 - sqrt 6) * (sqrt 3 + sqrt 6 - sqrt 2) * (sqrt 6 + sqrt 2 - sqrt 3))
    (hb : b = (sqrt 2 + sqrt 3 + sqrt 5) * (sqrt 2 + sqrt 3 - sqrt 5) * (sqrt 3 + sqrt 5 - sqrt 2) * (sqrt 5 + sqrt 2 - sqrt 3)) :
    -4 ≤ a - b ∧ a - b < 0 := by
  have ha' : a = 23 := by
    rw [ha]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, 
      sq_nonneg (sqrt 2 - sqrt 3), sq_nonneg (sqrt 2 - sqrt 6), sq_nonneg (sqrt 3 - sqrt 6),
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3),
      sq_nonneg (sqrt 6),
      mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg 2),
      mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg 3),
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6)
    ]
  have hb' : b = 24 := by
    rw [hb]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, 
      sq_nonneg (sqrt 2 - sqrt 3), sq_nonneg (sqrt 2 - sqrt 5), sq_nonneg (sqrt 3 - sqrt 5),
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3),
      sq_nonneg (sqrt 5),
      mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 2),
      mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 3),
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 5)
    ]
  rw [ha', hb']
  constructor
  · norm_num
  · norm_num