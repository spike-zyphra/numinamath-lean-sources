import Mathlib

open Real

theorem inequalities_282281 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    2 * sqrt (a + b + c + d) ≥ sqrt a + sqrt b + sqrt c + sqrt d := by
  have h1 : 0 < a + b + c + d := by linarith
  have h2 : sqrt (a + b + c + d) ≥ 0 := by apply Real.sqrt_nonneg
  have h3 : sqrt a ≥ 0 := by apply Real.sqrt_nonneg
  have h4 : sqrt b ≥ 0 := by apply Real.sqrt_nonneg
  have h5 : sqrt c ≥ 0 := by apply Real.sqrt_nonneg
  have h6 : sqrt d ≥ 0 := by apply Real.sqrt_nonneg
  have h7 : (sqrt (a + b + c + d)) ^ 2 = a + b + c + d := by
    rw [Real.sq_sqrt]
    linarith
  have h8 : (sqrt a) ^ 2 = a := by
    rw [Real.sq_sqrt]
    linarith
  have h9 : (sqrt b) ^ 2 = b := by
    rw [Real.sq_sqrt]
    linarith
  have h10 : (sqrt c) ^ 2 = c := by
    rw [Real.sq_sqrt]
    linarith
  have h11 : (sqrt d) ^ 2 = d := by
    rw [Real.sq_sqrt]
    linarith
  have h12 : (sqrt a + sqrt b + sqrt c + sqrt d) ^ 2 ≤ 4 * (a + b + c + d) := by
    nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt a - sqrt c), sq_nonneg (sqrt a - sqrt d), sq_nonneg (sqrt b - sqrt c), sq_nonneg (sqrt b - sqrt d), sq_nonneg (sqrt c - sqrt d), 
              Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), 
              Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), 
              Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith), 
              Real.sq_sqrt (show 0 ≤ (d : ℝ) by linarith)
             ]
  nlinarith [Real.sqrt_nonneg (a + b + c + d), Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c, Real.sqrt_nonneg d, 
            h7, h8, h9, h10, h11, 
            sq_nonneg (sqrt (a + b + c + d) - (sqrt a + sqrt b + sqrt c + sqrt d) / 2)
           ]