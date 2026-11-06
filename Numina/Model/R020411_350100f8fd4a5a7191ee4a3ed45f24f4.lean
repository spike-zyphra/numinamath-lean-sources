import Mathlib

theorem inequalities_6085 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 5 + b ^ 5 + c ^ 5 - (a + b + c) ^ 5) / (a ^ 3 + b ^ 3 + c ^ 3 - (a + b + c) ^ 3) ≥
    10 / 9 * (a + b + c) ^ 2 := by

  have h1 : a ^ 3 + b ^ 3 + c ^ 3 - (a + b + c) ^ 3 < 0 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  apply (le_div_iff_of_neg' h1).mpr
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
    mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
    mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
    mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)]