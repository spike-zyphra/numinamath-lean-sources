import Mathlib

theorem inequalities_604445 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 - b * c) / (2 * a^2 + b * c) + (b^2 - c * a) / (2 * b^2 + c * a) +
    (c^2 - a * b) / (2 * c^2 + a * b) ≤ 0 := by

  have h1 : 0 < (2 * a^2 + b * c) * (2 * b^2 + c * a) * (2 * c^2 + a * b) := by positivity
  have h2 : (a^2 - b * c) / (2 * a^2 + b * c) + (b^2 - c * a) / (2 * b^2 + c * a) + (c^2 - a * b) / (2 * c^2 + a * b) ≤ 0 := by
    have h5 : 0 < (2 * a^2 + b * c) := by positivity
    have h6 : 0 < (2 * b^2 + c * a) := by positivity
    have h7 : 0 < (2 * c^2 + a * b) := by positivity
    have h8 : (a^2 - b * c) / (2 * a^2 + b * c) + (b^2 - c * a) / (2 * b^2 + c * a) + (c^2 - a * b) / (2 * c^2 + a * b) - (0 : ℝ) ≤ 0 := by 
      have h9 : (a^2 - b * c) / (2 * a^2 + b * c) + (b^2 - c * a) / (2 * b^2 + c * a) + (c^2 - a * b) / (2 * c^2 + a * b) - (0 : ℝ) =
          ( (a^2 - b * c) * (2 * b^2 + c * a) * (2 * c^2 + a * b) + (b^2 - c * a) * (2 * a^2 + b * c) * (2 * c^2 + a * b) + (c^2 - a * b) * (2 * a^2 + b * c) * (2 * b^2 + c * a) ) / ( (2 * a^2 + b * c) * (2 * b^2 + c * a) * (2 * c^2 + a * b) ) := by
        field_simp 
        <;> ring
      rw [h9] at *
      apply div_nonpos_of_nonpos_of_nonneg 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
        mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
        mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith) ]
      positivity
    linarith 
  linarith