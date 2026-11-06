import Mathlib

theorem inequalities_597733 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    1 ≤ 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) + 1 / (1 + 2 * a * b) := by 
  have h1 : 0 < (1 + 2 * b * c) * (1 + 2 * c * a) * (1 + 2 * a * b) := by
    positivity
  have h2 : 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) + 1 / (1 + 2 * a * b) - 1 ≥ 0 := by
    have h3 : 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) + 1 / (1 + 2 * a * b) - 1 =
        ((1 + 2 * c * a) * (1 + 2 * a * b) + (1 + 2 * b * c) * (1 + 2 * a * b) + (1 + 2 * b * c) * (1 + 2 * c * a) - (1 + 2 * b * c) * (1 + 2 * c * a) * (1 + 2 * a * b)) / ((1 + 2 * b * c) * (1 + 2 * c * a) * (1 + 2 * a * b)) := by
      field_simp
      <;> ring 
    rw [h3] 
    have h4 : (1 + 2 * c * a) * (1 + 2 * a * b) + (1 + 2 * b * c) * (1 + 2 * a * b) + (1 + 2 * b * c) * (1 + 2 * c * a) - (1 + 2 * b * c) * (1 + 2 * c * a) * (1 + 2 * a * b) ≥ 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < a from by linarith) (show 0 < b * c from by nlinarith), 
          mul_pos (show 0 < b from by linarith) (show 0 < a * c from by nlinarith), 
          mul_pos (show 0 < c from by linarith) (show 0 < a * b from by nlinarith), 
          h, sq_nonneg (a^2 + b^2 + c^2 - 3)]
    have h5 : ((1 + 2 * c * a) * (1 + 2 * a * b) + (1 + 2 * b * c) * (1 + 2 * a * b) + (1 + 2 * b * c) * (1 + 2 * c * a) - (1 + 2 * b * c) * (1 + 2 * c * a) * (1 + 2 * a * b)) / ((1 + 2 * b * c) * (1 + 2 * c * a) * (1 + 2 * a * b)) ≥ 0 := by 
      apply div_nonneg 
      linarith [h4] 
      positivity 
    linarith 
  linarith