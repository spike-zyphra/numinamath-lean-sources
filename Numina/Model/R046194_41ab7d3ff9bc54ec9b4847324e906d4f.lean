import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_315292 (a b : ℝ) (ha : abs a < 1) (hb : abs b < 1) :
    abs (a * b + sqrt ((1 - a^2) * (1 - b^2))) ≤ 1 ∧
    abs (a * b - sqrt ((1 - a^2) * (1 - b^2))) ≤ 1 := by 
  have ha1 : -1 < a := by linarith [abs_lt.mp ha]
  have ha2 : a < 1 := by linarith [abs_lt.mp ha]
  have hb1 : -1 < b := by linarith [abs_lt.mp hb]
  have hb2 : b < 1 := by linarith [abs_lt.mp hb]
  have h1 : a^2 < 1 := by nlinarith
  have h2 : b^2 < 1 := by nlinarith
  have h7 : 0 ≤ 1 - a^2 := by nlinarith
  have h8 : 0 ≤ 1 - b^2 := by nlinarith
  have h9 : 0 ≤ (1 - a^2) * (1 - b^2) := by positivity
  have h6 : sqrt ((1 - a^2) * (1 - b^2)) ≥ 0 := by positivity

  have h5 : abs (a * b + sqrt ((1 - a^2) * (1 - b^2))) ≤ 1 := by
    have h11 : -1 ≤ a * b + sqrt ((1 - a^2) * (1 - b^2)) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), 
          sq_nonneg (sqrt ((1 - a^2) * (1 - b^2)) - a * b), 
          Real.sqrt_nonneg ((1 - a^2) * (1 - b^2)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (1 - a^2) * (1 - b^2) by nlinarith), 
          mul_nonneg (show 0 ≤ 1 - a^2 by nlinarith) (show 0 ≤ 1 - b^2 by nlinarith), 
          mul_pos (show 0 < (1 : ℝ) by linarith) (show 0 < (1 : ℝ) by linarith)]
    have h12 : a * b + sqrt ((1 - a^2) * (1 - b^2)) ≤ 1 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), 
          sq_nonneg (sqrt ((1 - a^2) * (1 - b^2)) - a * b), 
          Real.sqrt_nonneg ((1 - a^2) * (1 - b^2)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (1 - a^2) * (1 - b^2) by nlinarith), 
          mul_nonneg (show 0 ≤ 1 - a^2 by nlinarith) (show 0 ≤ 1 - b^2 by nlinarith), 
          mul_pos (show 0 < (1 : ℝ) by linarith) (show 0 < (1 : ℝ) by linarith)]
    apply abs_le.mpr
    constructor <;> nlinarith 
  have h6 : abs (a * b - sqrt ((1 - a^2) * (1 - b^2))) ≤ 1 := by
    have h11 : -1 ≤ a * b - sqrt ((1 - a^2) * (1 - b^2)) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), 
          sq_nonneg (sqrt ((1 - a^2) * (1 - b^2)) - a * b), 
          Real.sqrt_nonneg ((1 - a^2) * (1 - b^2)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (1 - a^2) * (1 - b^2) by nlinarith), 
          mul_nonneg (show 0 ≤ 1 - a^2 by nlinarith) (show 0 ≤ 1 - b^2 by nlinarith), 
          mul_pos (show 0 < (1 : ℝ) by linarith) (show 0 < (1 : ℝ) by linarith)]
    have h12 : a * b - sqrt ((1 - a^2) * (1 - b^2)) ≤ 1 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), 
          sq_nonneg (sqrt ((1 - a^2) * (1 - b^2)) - a * b), 
          Real.sqrt_nonneg ((1 - a^2) * (1 - b^2)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (1 - a^2) * (1 - b^2) by nlinarith), 
          mul_nonneg (show 0 ≤ 1 - a^2 by nlinarith) (show 0 ≤ 1 - b^2 by nlinarith), 
          mul_pos (show 0 < (1 : ℝ) by linarith) (show 0 < (1 : ℝ) by linarith)]
    apply abs_le.mpr
    constructor <;> nlinarith 
  constructor 
  · exact h5 
  · exact h6