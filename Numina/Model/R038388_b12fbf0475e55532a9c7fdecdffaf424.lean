import Mathlib

open Real
open scoped BigOperators

theorem inequalities_600010 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  (-a + b + c) * (-a - b + c) + (a - b + c) * (a + b - c) +
  (a + b - c) * (-a + b + c) ≤
  sqrt (a * b * c) * (sqrt a + sqrt b + sqrt c) := by

  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc

  have h4 : a + b - c > 0 := by linarith
  have h5 : a - b + c > 0 := by linarith
  have h6 : -a + b + c > 0 := by linarith

  have h11 : sqrt a ≥ 0 := by positivity
  have h12 : sqrt b ≥ 0 := by positivity
  have h13 : sqrt c ≥ 0 := by positivity
  
  have h14 : sqrt (a * b * c) = sqrt a * sqrt b * sqrt c := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    all_goals ring_nf <;> norm_num
  
  have h16 : sqrt (a * b) = sqrt a * sqrt b := by
    rw [Real.sqrt_mul]
    all_goals linarith
  have h17 : sqrt (b * c) = sqrt b * sqrt c := by
    rw [Real.sqrt_mul]
    all_goals linarith
  have h18 : sqrt (a * c) = sqrt a * sqrt c := by
    rw [Real.sqrt_mul]
    all_goals linarith

  nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt b - sqrt c), sq_nonneg (sqrt c - sqrt a), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c, 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (sqrt a * sqrt b - sqrt b * sqrt c), sq_nonneg (sqrt b * sqrt c - sqrt a * sqrt c), sq_nonneg (sqrt a * sqrt c - sqrt a * sqrt b), 
          Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith), 
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c), 
          mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), 
          sq_nonneg (sqrt a * sqrt b - sqrt a * sqrt c), sq_nonneg (sqrt b * sqrt c - sqrt a * sqrt c)
        ]