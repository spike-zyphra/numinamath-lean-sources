import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_323782 (x : ℝ) (hx : |x| ≤ sqrt 5) :
    4 - sqrt 5 ≤ x + 4 + sqrt (5 - x^2) ∧
    x + 4 + sqrt (5 - x^2) ≤ 4 + sqrt 10 := by
  have h1 : -sqrt 5 ≤ x := by 
    linarith [abs_le.mp hx]
  have h2 : x ≤ sqrt 5 := by 
    linarith [abs_le.mp hx]
  have h3 : 0 ≤ 5 - x^2 := by 
    have h4 : x^2 ≤ (5 : ℝ) := by 
      have h5 : -sqrt 5 ≤ x := h1 
      have h6 : x ≤ sqrt 5 := h2 
      have h7 : (sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num) 
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg x]
    nlinarith 
  have h11 : sqrt (5 - x^2) ≥ 0 := Real.sqrt_nonneg (5 - x^2)
  constructor
  · -- Prove 4 - sqrt 5 ≤ x + 4 + sqrt (5 - x^2)
    nlinarith [Real.sqrt_nonneg (5 - x^2), Real.sqrt_nonneg (5 : ℝ), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (5 - x^2 : ℝ) by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (x + Real.sqrt 5), Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)
    ]
  · -- Prove x + 4 + sqrt (5 - x^2) ≤ 4 + sqrt 10
    have h4 : (x + sqrt (5 - x^2)) ^ 2 ≤ (sqrt 10) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (5 - x^2), Real.sqrt_nonneg (10 : ℝ), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 - x^2 : ℝ) by nlinarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), 
        sq_nonneg (x ^ 2 - (5 / 2)), sq_nonneg (sqrt (5 - x ^ 2) ^ 2 - (5 / 2)), Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
      ]
    have h5 : x + sqrt (5 - x^2) ≤ Real.sqrt 10 := by
      have h6 : (x + sqrt (5 - x^2)) ^ 2 ≤ (Real.sqrt 10) ^ 2 := h4 
      have h7 : 0 ≤ Real.sqrt 10 := Real.sqrt_nonneg 10 
      nlinarith [Real.sqrt_nonneg (5 - x^2), Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
    linarith