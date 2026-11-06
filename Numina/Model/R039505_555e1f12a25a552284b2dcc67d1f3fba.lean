import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_325581 {x : ℝ} (hx : 0 < x ∧ x < 1)
  (y : ℝ) (hy : y = sqrt (x^2 + 1) + sqrt (1 + (1 - x)^2)) :
  sqrt 5 ≤ y ∧ y < 1 + sqrt 2 := by
  rcases hx with ⟨h1, h2⟩
  have h3 : sqrt 5 ≤ y := by
    rw [hy]
    have h5' : sqrt 5 ≤ sqrt (x ^ 2 + 1) + sqrt (1 + (1 - x) ^ 2) := by
      have pos1 : 0 < sqrt (x ^ 2 + 1) := by positivity
      have pos2 : 0 < sqrt (1 + (1 - x) ^ 2) := by positivity
      have h6 : (sqrt (x ^ 2 + 1) + sqrt (1 + (1 - x) ^ 2)) ^ 2 ≥ 5 := by
        nlinarith [sq_nonneg (sqrt (x ^ 2 + 1) - sqrt (1 + (1 - x) ^ 2)), sq_nonneg (x - 1 / 2), 
                 Real.sqrt_nonneg 5, Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (1 + (1 - x) ^ 2), 
                 Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 2 + 1: ℝ) by nlinarith), 
                 Real.sq_sqrt (show (0 : ℝ) ≤ (1 + (1 - x) ^ 2 : ℝ) by nlinarith), 
                 Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
                 mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 1)) (Real.sqrt_nonneg (1 + (1 - x) ^ 2)), 
                 Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (x ^ 2 + 1) by nlinarith), 
                 Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (1 + (1 - x) ^ 2 : ℝ) by nlinarith), 
                 mul_nonneg (show (0 : ℝ) ≤ (x) by linarith) (show (0 : ℝ) ≤ (1 - x) by linarith), 
                 Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (1 + (1 - x : ℝ) ^ 2), 
                 Real.sqrt_nonneg (5 : ℝ)
                 ]
      have h8 : sqrt ((sqrt (x ^ 2 + 1) + sqrt (1 + (1 - x) ^ 2)) ^ 2) ≥ sqrt (5 : ℝ) := Real.sqrt_le_sqrt (show (sqrt (x ^ 2 + 1) + sqrt (1 + (1 - x) ^ 2)) ^ 2 ≥ 5 by nlinarith [h6])
      have h9 : sqrt ((sqrt (x ^ 2 + 1) + sqrt (1 + (1 - x) ^ 2)) ^ 2) = sqrt (x ^ 2 + 1) + sqrt (1 + (1 - x) ^ 2) := by rw [Real.sqrt_sq (by positivity)]
      linarith
      <;> assumption
    linarith
    <;> assumption
  have h4 : y < 1 + sqrt 2 := by
    rw [hy]
    have h5 : sqrt (x ^ 2 + 1) < sqrt 2 := by
      have h6 : x ^ 2 < 1 := by nlinarith
      have h7 : x ^ 2 + 1 < 2 := by nlinarith
      have h8 : sqrt (x ^ 2 + 1) < sqrt (2 : ℝ) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
      have h9 : sqrt (2 : ℝ) = sqrt 2 := by norm_num
      linarith
    have h6 : sqrt (1 + (1 - x) ^ 2) < sqrt 2 := by
      have h7 : (1 - x) ^ 2 < 1 := by nlinarith
      have h8 : 1 + (1 - x) ^ 2 < 2 := by nlinarith
      have h9 : sqrt (1 + (1 - x) ^ 2) < sqrt (2 : ℝ) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
      have h10 : sqrt (2 : ℝ) = sqrt 2 := by norm_num
      linarith
    have h7 : sqrt (x ^ 2 + 1) > 0 := by positivity
    have h8 : sqrt (1 + (1 - x) ^ 2) > 0 := by positivity
    have h9 : sqrt (x ^ 2 + 1) + sqrt (1 + (1 - x) ^ 2) < 1 + sqrt 2 := by
      have h6c : (sqrt (x ^ 2 + 1) + sqrt (1 + (1 - x) ^ 2)) ^ 2 < (1 + sqrt 2) ^ 2 := by
        nlinarith [sq_pos_of_pos (show (0 : ℝ) < 1 by norm_num), sq_pos_of_pos h7, sq_pos_of_pos h8, 
                 Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (1 + (1 - x) ^ 2), 
                 Real.sqrt_nonneg 2, 
                 Real.sq_sqrt (show (0 : ℝ) ≤ (2) by norm_num), 
                 Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 2 + 1 : ℝ) by nlinarith), 
                 Real.sq_sqrt (show (0 : ℝ) ≤ (1 + (1 - x) ^ 2 : ℝ) by nlinarith), 
                 Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (x ^ 2 + 1 : ℝ), Real.sqrt_nonneg (1 + (1 - x) ^ 2 : ℝ), 
                 Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
                 mul_nonneg (show (0 : ℝ) ≤ (x) by linarith) (show (0 : ℝ) ≤ (1 - x) by linarith), 
                 Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
                 ]
      have h10 : sqrt (x ^ 2 + 1) + sqrt (1 + (1 - x) ^ 2) > 0 := by positivity
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (1 + (1 - x : ℝ) ^ 2), Real.sqrt_nonneg 2, 
                 Real.sqrt_nonneg 2
                ]
    linarith
  constructor <;> 
    try { linarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (1 + (1 - x) ^ 2)] }
  <;> try { tauto }
  <;> try { 
      linarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (1 + (1 - x) ^ 2), 
                Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (1 + (1 - x) ^ 2)
               ]
  }
  <;> try { linarith }