import Mathlib

theorem inequalities_257118 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) : a ^ 4 + b ^ 4 + c ^ 4 ≥ a * b * c := by
  have h1 : c = 1 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - (1 - a - b) ^ 2), sq_nonneg ((1 - a - b) ^ 2 - a ^ 2),
          sq_nonneg (a - b), sq_nonneg (b - (1 - a - b)), sq_nonneg ((1 - a - b) - a),
          sq_nonneg (a + b - 1 / 2), sq_nonneg (b + (1 - a - b) - 1 / 2), sq_nonneg ((1 - a - b) + a - 1 / 2),
          mul_pos ha hb, mul_pos hb (show 0 < (1 - a - b) from by nlinarith), mul_pos ha (show 0 < (1 - a - b) from by nlinarith)
        ]