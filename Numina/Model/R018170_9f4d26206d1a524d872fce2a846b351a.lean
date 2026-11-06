import Mathlib

open Real

theorem algebra_312931 {a : ℝ} (ha : 1 < a) :
    min (min (min (sqrt (1993 * a) - sqrt (1993 * a - 1)) (sqrt (1993 * a - 1) - sqrt (1993 * a))) (sqrt (1993 * a) - sqrt (1993 * a + 1))) (sqrt (1993 * a + 1) - sqrt (1993 * a)) = sqrt (1993 * a - 1) - sqrt (1993 * a) := by

  have h1 : 1993 * a > 1993 * a - 1 := by linarith
  have h2 : 1993 * a > 0 := by nlinarith
  have h3 : 1993 * a - 1 > 0 := by nlinarith
  have h4 : 1993 * a + 1 > 1993 * a := by linarith

  have h5' : sqrt (1993 * a) > sqrt (1993 * a - 1) := by
    apply Real.sqrt_lt_sqrt
    all_goals nlinarith

  have h5'' : sqrt (1993 * a + 1) > sqrt (1993 * a) := by
    apply Real.sqrt_lt_sqrt
    all_goals nlinarith

  have h6' : sqrt (1993 * a) - sqrt (1993 * a - 1) > 0 := by
    linarith [Real.sqrt_nonneg (1993 * a), Real.sqrt_nonneg (1993 * a - 1), h5']

  have h10' : sqrt (1993 * a + 1) - sqrt (1993 * a) > 0 := by
    linarith [Real.sqrt_nonneg (1993 * a + 1), Real.sqrt_nonneg (1993 * a), h5'']

  have h9' : sqrt (1993 * a) - sqrt (1993 * a + 1) < 0 := by 
    nlinarith [Real.sqrt_nonneg (1993 * a + 1), Real.sqrt_nonneg (1993 * a), 
      h5'', 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1993 * a by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1993 * a + 1 by nlinarith)
    ]

  have h8' : sqrt (1993 * a - 1) - sqrt (1993 * a) < 0 := by
    nlinarith [Real.sqrt_nonneg (1993 * a - 1), Real.sqrt_nonneg (1993 * a), 
      h5', 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1993 * a - 1 by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1993 * a by nlinarith)
    ]

  have h8'' : sqrt (1993 * a - 1) - sqrt (1993 * a) < sqrt (1993 * a) - sqrt (1993 * a + 1) := by 
    nlinarith [Real.sqrt_nonneg (1993 * a - 1), 
      Real.sqrt_nonneg (1993 * a), 
      Real.sqrt_nonneg (1993 * a + 1), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1993 * a - 1 by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1993 * a by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1993 * a + 1 by nlinarith)
    ]

  have h19 : min (sqrt (1993 * a) - sqrt (1993 * a - 1)) (sqrt (1993 * a - 1) - sqrt (1993 * a)) = sqrt (1993 * a - 1) - sqrt (1993 * a) := by 
    apply min_eq_right 
    nlinarith [Real.sqrt_nonneg (1993 * a), Real.sqrt_nonneg (1993 * a - 1), h6']

  have h20 : min (min (sqrt (1993 * a) - sqrt (1993 * a - 1)) (sqrt (1993 * a - 1) - sqrt (1993 * a))) (sqrt (1993 * a) - sqrt (1993 * a + 1)) = sqrt (1993 * a - 1) - sqrt (1993 * a) := by 
    rw [h19]
    apply min_eq_left 
    nlinarith [Real.sqrt_nonneg (1993 * a - 1), Real.sqrt_nonneg (1993 * a), h9']
  
  have h21 : min (min (min (sqrt (1993 * a) - sqrt (1993 * a - 1)) (sqrt (1993 * a - 1) - sqrt (1993 * a))) (sqrt (1993 * a) - sqrt (1993 * a + 1))) (sqrt (1993 * a + 1) - sqrt (1993 * a)) = sqrt (1993 * a - 1) - sqrt (1993 * a) := by
    rw [h20]
    apply min_eq_left 
    nlinarith [Real.sqrt_nonneg (1993 * a - 1), Real.sqrt_nonneg (1993 * a + 1), h10']
  exact h21