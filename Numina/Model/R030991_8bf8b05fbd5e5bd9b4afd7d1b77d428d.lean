import Mathlib

theorem inequalities_30661 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt ((a ^ 2 + b ^ 2) / (a + b)) +
    Real.sqrt ((b ^ 2 + c ^ 2) / (b + c)) +
    Real.sqrt ((c ^ 2 + a ^ 2) / (c + a)) ≥
    Real.sqrt ((2 * a * b) / (3 * a + b + 2 * c)) +
    Real.sqrt ((2 * b * c) / (3 * b + c + 2 * a)) +
    Real.sqrt ((2 * c * a) / (3 * c + a + 2 * b)) := by
  have h1 : Real.sqrt ((a ^ 2 + b ^ 2) / (a + b)) ≥ Real.sqrt ((2 * a * b) / (3 * a + b + 2 * c)) := by
    apply Real.sqrt_le_sqrt
    have h2 : (a ^ 2 + b ^ 2) / (a + b) ≥ (2 * a * b) / (3 * a + b + 2 * c) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
    linarith
  have h2 : Real.sqrt ((b ^ 2 + c ^ 2) / (b + c)) ≥ Real.sqrt ((2 * b * c) / (3 * b + c + 2 * a)) := by
    apply Real.sqrt_le_sqrt
    have h3 : (b ^ 2 + c ^ 2) / (b + c) ≥ (2 * b * c) / (3 * b + c + 2 * a) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (b - c), sq_nonneg (b - a), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a * b - b * c)]
    linarith
  have h3 : Real.sqrt ((c ^ 2 + a ^ 2) / (c + a)) ≥ Real.sqrt ((2 * c * a) / (3 * c + a + 2 * b)) := by
    apply Real.sqrt_le_sqrt
    have h4 : (c ^ 2 + a ^ 2) / (c + a) ≥ (2 * c * a) / (3 * c + a + 2 * b) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (c - a), sq_nonneg (c - b), sq_nonneg (a - b),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        sq_nonneg (c * a - a * b), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a)]
    linarith
  linarith [h1, h2, h3]