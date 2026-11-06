import Mathlib

open Real

theorem algebra_7764 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = a * b * c) :
    ¬(a < sqrt 3 ∧ b < sqrt 3 ∧ c < sqrt 3) := by 
  rintro ⟨ha1, hb1, hc1⟩
  have h1 : (sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : a < sqrt 3 := ha1
  have h3 : b < sqrt 3 := hb1
  have h4 : c < sqrt 3 := hc1
  have h5 : a * a < 3 := by 
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (a - sqrt 3), sq_nonneg (sqrt 3)]
  have h6 : b * b < 3 := by 
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (b - sqrt 3), sq_nonneg (sqrt 3)]
  have h7 : c * c < 3 := by 
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (c - sqrt 3), sq_nonneg (sqrt 3)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1)]