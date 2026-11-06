import Mathlib

theorem inequalities_296234 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a * b) / (3 * a + 4 * b + 5 * c) +
    (b * c) / (3 * b + 4 * c + 5 * a) +
    (c * a) / (3 * c + 4 * a + 5 * b) ≤
    (a + b + c) / 12 := by 
  have h1 : 0 < (3 * a + 4 * b + 5 * c) * (3 * b + 4 * c + 5 * a) * (3 * c + 4 * a + 5 * b) := by
    positivity
  have h2 : (a * b) / (3 * a + 4 * b + 5 * c) + (b * c) / (3 * b + 4 * c + 5 * a) + (c * a) / (3 * c + 4 * a + 5 * b) - (a + b + c) / 12 ≤ 0 := by
    have h3 : 0 < (3 * a + 4 * b + 5 * c) := by positivity
    have h4 : 0 < (3 * b + 4 * c + 5 * a) := by positivity
    have h5 : 0 < (3 * c + 4 * a + 5 * b) := by positivity

    have h6 : (a * b) / (3 * a + 4 * b + 5 * c) + (b * c) / (3 * b + 4 * c + 5 * a) + (c * a) / (3 * c + 4 * a + 5 * b) - (a + b + c) / 12 =
        ( (a * b) * (3 * b + 4 * c + 5 * a) * (3 * c + 4 * a + 5 * b) * 12 +
          (b * c) * (3 * a + 4 * b + 5 * c) * (3 * c + 4 * a + 5 * b) * 12 +
          (c * a) * (3 * a + 4 * b + 5 * c) * (3 * b + 4 * c + 5 * a) * 12 - 
          (a + b + c) * (3 * a + 4 * b + 5 * c) * (3 * b + 4 * c + 5 * a) * (3 * c + 4 * a + 5 * b) )
          / ( (3 * a + 4 * b + 5 * c) * (3 * b + 4 * c + 5 * a) * (3 * c + 4 * a + 5 * b) * 12 ) := by
      field_simp
      <;> ring
    rw [h6] at *
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [ sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    positivity
  linarith