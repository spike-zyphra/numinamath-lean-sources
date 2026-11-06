import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_315038 (x : ℝ) (hx : 1/3 ≤ x ∧ x ≤ 5) :
    3 * sqrt (5 - x) + 2 * sqrt (3 * x - 1) ≤ 7 * sqrt 2 := by
  have h1 : 1/3 ≤ x := hx.1
  have h2 : x ≤ 5 := hx.2
  have h3 : 0 ≤ 5 - x := by linarith
  have h4 : 0 ≤ 3 * x - 1 := by linarith
  have h10 : (3 * sqrt (5 - x) + 2 * sqrt (3 * x - 1)) ^ 2 ≤ (7 * sqrt 2) ^ 2 := by
    have h6 : sqrt (5 - x) ^ 2 = 5 - x := by
      apply Real.sq_sqrt
      linarith
    have h7 : sqrt (3 * x - 1) ^ 2 = 3 * x - 1 := by
      apply Real.sq_sqrt
      linarith
    have h8 : (7 * sqrt 2) ^ 2 = 98 := by
      calc
        (7 * sqrt 2) ^ 2 = 49 * (sqrt 2) ^ 2 := by ring
        _ = 49 * 2 := by rw [Real.sq_sqrt]; positivity
        _ = 98 := by norm_num
    have h9 : (3 * sqrt (5 - x) + 2 * sqrt (3 * x - 1)) ^ 2 =
        9 * (sqrt (5 - x) ^ 2) + 4 * (sqrt (3 * x - 1) ^ 2) + 12 * (sqrt (5 - x) * sqrt (3 * x - 1)) := by ring
    rw [h9, h6, h7]
    have h14 : Real.sqrt ((5 - x) * (3 * x - 1)) ≤ (5 - x + 3 * x - 1) / 2 := by
      nlinarith [Real.sqrt_nonneg ((5 - x) * (3 * x - 1)), Real.sq_sqrt (show (0 : ℝ) ≤ (5 - x) * (3 * x - 1) by nlinarith), sq_nonneg ((5 - x) - (3 * x - 1))]
    nlinarith [Real.sqrt_nonneg (5 - x), Real.sqrt_nonneg (3 * x - 1), Real.sqrt_nonneg (2), 
      mul_nonneg (Real.sqrt_nonneg (5 - x)) (Real.sqrt_nonneg (3 * x - 1)), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (5 - x) by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 * x - 1) by linarith), 
      sq_nonneg (sqrt (5 - x) - sqrt (3 * x - 1)), 
      sq_nonneg ((5 - x) - (3 * x - 1)), 
      sq_nonneg (x - 3), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2) by norm_num), 
      Real.sqrt_nonneg (5 - x), 
      Real.sqrt_nonneg (3 * x - 1),
      mul_nonneg (show 0 ≤ (5 - x : ℝ) by linarith) (show 0 ≤ (3 * x - 1 : ℝ) by linarith)
    ]
  have h11 : 0 ≤ (3 * sqrt (5 - x) + 2 * sqrt (3 * x - 1) : ℝ) := by
    positivity
  have h14 : 0 ≤ (7 * sqrt 2 : ℝ) := by 
    positivity
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (5 - x), Real.sqrt_nonneg (3 * x - 1), 
    sq_nonneg (3 * sqrt (5 - x) + 2 * sqrt (3 * x - 1) - 7 * sqrt 2), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (2) by norm_num), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (5 - x) by linarith), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (3 * x - 1) by linarith)
  ]