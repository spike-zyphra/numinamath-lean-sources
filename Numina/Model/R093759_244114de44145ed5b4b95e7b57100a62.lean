import Mathlib

theorem inequalities_600691 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (4 * a ^ 2 - b ^ 2 - c ^ 2) / (a * (b + c)) + (4 * b ^ 2 - c ^ 2 - a ^ 2) / (b * (c + a)) +
    (4 * c ^ 2 - a ^ 2 - b ^ 2) / (c * (a + b)) ≤ 3 := by
  have h1 : 0 < a * (b + c) := mul_pos ha (show 0 < b + c by linarith)
  have h2 : 0 < b * (c + a) := mul_pos hb (show 0 < c + a by linarith)
  have h3 : 0 < c * (a + b) := mul_pos hc (show 0 < a + b by linarith)
  have h4 : 0 < a * (b + c) * (b * (c + a)) := mul_pos h1 h2
  have h5 : 0 < a * (b + c) * (c * (a + b)) := mul_pos h1 h3
  have h6 : 0 < b * (c + a) * (c * (a + b)) := mul_pos h2 h3
  have h7 : 0 < a * (b + c) * (b * (c + a)) * (c * (a + b)) := mul_pos h4 h3
  have h8 : (4 * a ^ 2 - b ^ 2 - c ^ 2) / (a * (b + c)) + (4 * b ^ 2 - c ^ 2 - a ^ 2) / (b * (c + a)) + (4 * c ^ 2 - a ^ 2 - b ^ 2) / (c * (a + b)) - 3 ≤ 0 := by
    have h9 : (4 * a ^ 2 - b ^ 2 - c ^ 2) / (a * (b + c)) + (4 * b ^ 2 - c ^ 2 - a ^ 2) / (b * (c + a)) + (4 * c ^ 2 - a ^ 2 - b ^ 2) / (c * (a + b)) - 3 =
          ((4 * a ^ 2 - b ^ 2 - c ^ 2) * (b * (c + a) * (c * (a + b)) ) + (4 * b ^ 2 - c ^ 2 - a ^ 2) * (a * (b + c) * (c * (a + b)) ) + (4 * c ^ 2 - a ^ 2 - b ^ 2) * (a * (b + c) * (b * (c + a)) ) - 3 * (a * (b + c) * (b * (c + a)) * (c * (a + b)) )) / (a * (b + c) * (b * (c + a)) * (c * (a + b)) ) := by
        field_simp
        ring
    rw [h9]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- need to show that numerator ≤ 0
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    · -- need to show denominator ≥ 0
      positivity
  linarith [h8]