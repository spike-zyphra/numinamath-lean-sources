import Mathlib

open Real

theorem inequalities_327715 {a b c : ℝ}
    (ha : a = sqrt 2 - 1) (hb : b = sqrt 5 - 2) (hc : c = sqrt 10 - 3) :
    c < b ∧ b < a := by 
  have h1 : c < b := by
    rw [hc, hb]
    have h2 : sqrt 10 < sqrt 5 + 1 := by 
      have h3 : sqrt 10 < sqrt 5 + 1 := by
        have h4 : sqrt 10 ≥ 0 := Real.sqrt_nonneg 10
        have h5 : sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
        have h6 : (sqrt 10) ^ 2 < (sqrt 5 + 1) ^ 2 := by 
          nlinarith [Real.sqrt_nonneg 10, Real.sqrt_nonneg 5, 
              sq_nonneg (sqrt 10 - sqrt 5 - 1), sq_nonneg (sqrt 5 - 2), 
              mul_nonneg (Real.sqrt_nonneg 10) (Real.sqrt_nonneg 5), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
              ]
        nlinarith [Real.sqrt_nonneg 10, Real.sqrt_nonneg 5, 
            Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
            ]
      linarith
    linarith [h2, Real.sqrt_nonneg 10, Real.sqrt_nonneg 5]

  have h2 : b < a := by
    rw [hb, ha]
    have h5 : sqrt 5 < sqrt 2 + 1 := by 
      have h6 : sqrt 5 < sqrt 2 + 1 := by
        have h6 : (sqrt 5) ^ 2 < (sqrt 2 + 1) ^ 2 := by
          nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, 
              sq_nonneg (sqrt 5 - sqrt 2 - 1), sq_nonneg (sqrt 2 - 1), 
              mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 2), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
              ]
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, 
            Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
            ]
      linarith
    linarith [h5, Real.sqrt_nonneg 5, Real.sqrt_nonneg 2]

  constructor 
  · exact h1 
  · exact h2