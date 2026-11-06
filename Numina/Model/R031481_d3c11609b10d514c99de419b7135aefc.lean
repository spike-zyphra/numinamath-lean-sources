import Mathlib

theorem inequalities_599749 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (a^2 + 8 * b * c) + Real.sqrt (b^2 + 8 * c * a) +
    Real.sqrt (c^2 + 8 * a * b) ≤ 3 * (a + b + c) := by
  have h12 : (Real.sqrt (a^2 + 8 * b * c) + Real.sqrt (b^2 + 8 * c * a) +
    Real.sqrt (c^2 + 8 * a * b)) ^ 2 ≤ 3 * (a^2 + 8 * b * c +
     b^2 + 8 * c * a + c^2 + 8 * a * b) := by
    nlinarith [sq_nonneg (Real.sqrt (a^2 + 8 * b * c) - Real.sqrt (b^2 + 8 * c * a)), sq_nonneg (Real.sqrt (a^2 + 8 * b * c) - Real.sqrt (c^2 + 8 * a * b)), sq_nonneg (Real.sqrt (b^2 + 8 * c * a) - Real.sqrt (c^2 + 8 * a * b)), Real.sqrt_nonneg (a^2 + 8 * b * c), Real.sqrt_nonneg (b^2 + 8 * c * a), Real.sqrt_nonneg (c^2 + 8 * a * b), 
                Real.sq_sqrt (show (a^2 + 8 * b * c : ℝ) ≥ 0 by nlinarith), Real.sq_sqrt (show (b^2 + 8 * c * a : ℝ) ≥ 0 by nlinarith), Real.sq_sqrt (show (c^2 + 8 * a * b : ℝ) ≥ 0 by nlinarith), 
                mul_nonneg (Real.sqrt_nonneg (a^2 + 8 * b * c)) (Real.sqrt_nonneg (b^2 + 8 * c * a)), 
                mul_nonneg (Real.sqrt_nonneg (a^2 + 8 * b * c)) (Real.sqrt_nonneg (c^2 + 8 * a * b)), 
                mul_nonneg (Real.sqrt_nonneg (b^2 + 8 * c * a)) (Real.sqrt_nonneg (c^2 + 8 * a * b))]
  
  have h13 : 3 * (a ^ 2 + 8 * b * c + b^2 + 8 * c * a + c^2 + 8 * a * b) ≤ 9 * (a + b + c) ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h14 : (Real.sqrt (a^2 + 8 * b * c) + Real.sqrt (b^2 + 8 * c * a) +
    Real.sqrt (c^2 + 8 * a * b)) ≤ 3 * (a + b + c) := by
    nlinarith [Real.sqrt_nonneg (a^2 + 8 * b * c), Real.sqrt_nonneg (b^2 + 8 * c * a), Real.sqrt_nonneg (c^2 + 8 * a * b), h12, h13, 
                mul_nonneg (Real.sqrt_nonneg (a^2 + 8 * b * c)) (Real.sqrt_nonneg (b^2 + 8 * c * a)), 
                mul_nonneg (Real.sqrt_nonneg (a^2 + 8 * b * c)) (Real.sqrt_nonneg (c^2 + 8 * a * b)), 
                mul_nonneg (Real.sqrt_nonneg (b^2 + 8 * c * a)) (Real.sqrt_nonneg (c^2 + 8 * a * b)), sq_nonneg (Real.sqrt (a^2 + 8 * b * c) - Real.sqrt (b^2 + 8 * c * a)), sq_nonneg (Real.sqrt (a^2 + 8 * b * c) - Real.sqrt (c^2 + 8 * a * b)), sq_nonneg (Real.sqrt (b^2 + 8 * c * a) - Real.sqrt (c^2 + 8 * a * b)), 
                Real.sq_sqrt (show (a^2 + 8 * b * c : ℝ) ≥ 0 by nlinarith), Real.sq_sqrt (show (b^2 + 8 * c * a : ℝ) ≥ 0 by nlinarith), Real.sq_sqrt (show (c^2 + 8 * a * b : ℝ) ≥ 0 by nlinarith)]
  exact h14