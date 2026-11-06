import Mathlib

theorem inequalities_44841 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    Real.sqrt (a + b * c) + Real.sqrt (b + c * a) + Real.sqrt (c + a * b) ≤ 2 := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc
  have h4 : a + b + c = 1 := h
  have h5 : a * b * c > 0 := by positivity
  nlinarith [sq_nonneg (Real.sqrt (a + b * c) - Real.sqrt (b + c * a)), sq_nonneg (Real.sqrt (a + b * c) - Real.sqrt (c + a * b)), sq_nonneg (Real.sqrt (b + c * a) - Real.sqrt (c + a * b)), 
    Real.sq_sqrt (show (0 : ℝ) ≤ a + b * c by nlinarith), 
    Real.sq_sqrt (show (0 : ℝ) ≤ b + c * a by nlinarith), 
    Real.sq_sqrt (show (0 : ℝ) ≤ c + a * b by nlinarith), 
    Real.sqrt_nonneg (a + b * c), 
    Real.sqrt_nonneg (b + c * a), 
    Real.sqrt_nonneg (c + a * b), 
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    Real.sq_sqrt (show (0 : ℝ) ≤ a + b * c by nlinarith), 
    Real.sq_sqrt (show (0 : ℝ) ≤ b + c * a by nlinarith), 
    Real.sq_sqrt (show (0 : ℝ) ≤ c + a * b by nlinarith)
  ]