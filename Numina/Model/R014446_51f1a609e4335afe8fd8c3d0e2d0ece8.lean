import Mathlib

theorem inequalities_1889 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    a^2 + b^2 * c^2 + 10 ≥ 4 * (b * c + c * a + a * b) ∧
    2 * (b * c + c * a + a * b) ≤ a * b * c + 5 := by
  constructor
  · -- Prove the first inequality: $a^2 + b^2c^2 + 10 \ge 4(bc + ca + ab)$
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a * (b - 1)), sq_nonneg (a * (c - 1)), sq_nonneg ((b - 1) * (c - 1)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
  · -- Prove the second inequality: $2(bc + ca + ab) \le abc + 5$
    have h1 : c = 3 - a - b := by linarith
    rw [h1]
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((3 - a - b) - 1), 
          sq_nonneg (a * (b - 1)), sq_nonneg (a * ((3 - a - b) - 1)), sq_nonneg ((b - 1) * ((3 - a - b) - 1)), 
          mul_pos ha hb, mul_pos hb (show 0 < (3 - a - b : ℝ) by nlinarith), 
          mul_pos ha (show 0 < (3 - a - b : ℝ) by nlinarith)
        ]