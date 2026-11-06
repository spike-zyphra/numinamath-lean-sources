import Mathlib

theorem inequalities_47646 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    27 / (2 * (a + b + c) ^ 2) ≤ 1 / (b * (a + b)) + 1 / (c * (b + c)) + 1 / (a * (c + a)) := by
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have hc1 : 0 < c := hc
  have h1 : 0 < b * (a + b) := mul_pos hb1 (by linarith)
  have h2 : 0 < c * (b + c) := mul_pos hc1 (by linarith)
  have h3 : 0 < a * (c + a) := mul_pos ha1 (by linarith)
  have h4 : 0 < 2 * (a + b + c) ^ 2 := mul_pos (by norm_num) (pow_pos (by linarith) 2)
  have h7 : 0 < 2 * (a + b + c) ^ 2 * b * (a + b) * c * (b + c) * a * (c + a) := by positivity
  have h6 : (1 / (b * (a + b)) + 1 / (c * (b + c)) + 1 / (a * (c + a)) ) - (27 / (2 * (a + b + c) ^ 2)) ≥ 0 := by
    have h70 : (1 / (b * (a + b)) + 1 / (c * (b + c)) + 1 / (a * (c + a)) ) - (27 / (2 * (a + b + c) ^ 2)) = 
        (2 * (a + b + c) ^ 2 * c * (b + c) * a * (c + a) + 2 * (a + b + c) ^ 2 * b * (a + b) * a * (c + a) + 2 * (a + b + c) ^ 2 * b * (a + b) * c * (b + c) - 27 * b * (a + b) * c * (b + c) * a * (c + a)) / (2 * (a + b + c) ^ 2 * b * (a + b) * c * (b + c) * a * (c + a)) := by
      field_simp
      <;> ring
    rw [h70] at *
    apply div_nonneg 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha1 hb1, mul_pos hb1 hc1, mul_pos ha1 hc1, mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith)
        ]
    positivity
  linarith