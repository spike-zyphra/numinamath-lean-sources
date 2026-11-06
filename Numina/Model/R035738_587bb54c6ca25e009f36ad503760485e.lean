import Mathlib
open Real

theorem inequalities_27064 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
    a ^ 2 * b + b ^ 2 * c + c ^ 2 * a ≥ sqrt ((a + b + c) * (a * b + b * c + c * a)) := by

  have h12 : 0 < (a + b + c) * (a * b + b * c + c * a) := by positivity
  have h2 : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ≥ 0 := by positivity

  have h2' : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ^ 2 ≥ (a + b + c) * (a * b + b * c + c * a) := by 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]

  have h3 : sqrt ((a + b + c) * (a * b + b * c + c * a)) ≤ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by
    have h4 : (sqrt ((a + b + c) * (a * b + b * c + c * a))) ^ 2 = (a + b + c) * (a * b + b * c + c * a) := by
      exact Real.sq_sqrt (by nlinarith)
    have h5 : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ≥ 0 := by positivity
    have h6 : (sqrt ((a + b + c) * (a * b + b * c + c * a))) ≥ 0 := by positivity

    have h7 : (sqrt ((a + b + c) * (a * b + b * c + c * a))) ^ 2 ≤ (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ^ 2 := by 
      nlinarith [h2', h4]

    have h7' : sqrt ((a + b + c) * (a * b + b * c + c * a)) ≤ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by nlinarith [Real.sqrt_nonneg ((a + b + c) * (a * b + b * c + c * a)), h7, mul_nonneg (Real.sqrt_nonneg ((a + b + c) * (a * b + b * c + c * a))) (show 0 ≤ (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a : ℝ) by positivity)]
    linarith [h7']

  linarith [h3]