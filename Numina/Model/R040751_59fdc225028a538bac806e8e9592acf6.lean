import Mathlib

open Real
open scoped BigOperators

theorem inequalities_308629 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (h : a^2 + b^2 = c^2) (hle : a ≤ b ∧ b ≤ c) :
  a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) ≥ (2 + 3 * sqrt 2) * a * b * c := by
  have h1 : a ≤ b := hle.1
  have h2 : b ≤ c := hle.2
  have h3 : c ≥ a := by linarith
  have h4 : 0 < a * b := mul_pos ha hb
  have h5 : 0 < a * c := mul_pos ha hc
  have h6 : 0 < b * c := mul_pos hb hc
  have h8 : (sqrt 2 : ℝ) ^ 2 = 2 := by 
    exact Real.sq_sqrt (by norm_num)
  have h9 : (sqrt 2 : ℝ) > 0 := by positivity
  have h10 : c ^ 2 = a ^ 2 + b ^ 2 := by linarith 
  have h20 : 0 < c := hc
  have h25 : sqrt 2 > 0 := by positivity
  have h11 : a ^ 2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) ≥ (2 + 3 * sqrt 2) * a * b * c := by
    have pos1 : 0 < a * b * c := by positivity
    nlinarith [sq_nonneg (a - b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), 
        sq_nonneg (c - a - b), sq_nonneg (c^2 - (a^2 + b^2)), mul_pos ha hb, mul_pos hb hc, 
        mul_pos ha hc, mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - b by linarith), 
        sq_nonneg (a * (c - b)), sq_nonneg (b * (c - a)), 
        mul_nonneg (show 0 ≤ a by positivity) (show 0 ≤ b - a by linarith), 
        mul_nonneg (show 0 ≤ b by positivity) (show 0 ≤ c - b by linarith), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        mul_nonneg (show 0 ≤ a * b by positivity) (show 0 ≤ c by positivity), 
        sq_nonneg (a^2 + b^2 - c^2), 
        mul_nonneg (show (0 : ℝ) ≤ (sqrt 2 : ℝ) by positivity) (show (0 : ℝ) ≤ (sqrt 2 : ℝ) by positivity), 
        Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        sq_nonneg (a * b), sq_nonneg ((a) - (b)), sq_nonneg ((c) - a * Real.sqrt 2), 
        sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c))
    ]
  linarith