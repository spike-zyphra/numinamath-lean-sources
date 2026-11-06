import Mathlib

theorem inequalities_602989 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) +
    3 * (a * b + b * c + c * a) / (a + b + c)^2 ≥ 4 := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a * c := mul_pos ha hc
  have h3 : 0 < b * c := mul_pos hb hc

  have h_pos : 0 < (b + c) * (c + a) * (a + b) * (a + b + c)^2 := by positivity
  have h2 : (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) +
      3 * (a * b + b * c + c * a) / (a + b + c)^2 - 4 ≥ 0 := by 
    have h2 : 0 < (b + c) * (c + a) * (a + b) * (a + b + c)^2 := by positivity
    have h3 : ((a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) + 3 * (a * b + b * c + c * a) / (a + b + c)^2 - 4) =
      ((a + b) * (c + a) * (a + b) * (a + b + c)^2 +
      (b + c) * (b + c) * (a + b) * (a + b + c)^2 +
      (c + a) * (b + c) * (c + a) * (a + b + c)^2 +
      3 * (a * b + b * c + c * a) * (b + c) * (c + a) * (a + b) +
      - 4 * (b + c) * (c + a) * (a + b) * (a + b + c)^2) / ((b + c) * (c + a) * (a + b) * (a + b + c)^2) := by 
        field_simp
        ring
    rw [h3]
    apply div_nonneg 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (c - a)), 
          sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (c - a)), 
          sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (c - a)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a + b by linarith) (show 0 < b + c by linarith), 
          mul_pos (show 0 < a + b by linarith) (show 0 < c + a by linarith), 
          mul_pos (show 0 < b + c by linarith) (show 0 < c + a by linarith)]
    positivity
  linarith