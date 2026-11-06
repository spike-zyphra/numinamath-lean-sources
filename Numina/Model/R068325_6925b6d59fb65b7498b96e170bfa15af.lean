import Mathlib

theorem inequalities_604120 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 ≤ (a + 2 * b) / (c + 2 * b) + (b + 2 * c) / (a + 2 * c) +
        (c + 2 * a) / (b + 2 * a) := by 
  have ha1 : 0 < a + 2 * c := by nlinarith
  have hb1 : 0 < c + 2 * b := by nlinarith
  have hc1 : 0 < b + 2 * a := by nlinarith
  have h1 : (a + 2 * b) / (c + 2 * b) + (b + 2 * c) / (a + 2 * c) + (c + 2 * a) / (b + 2 * a) - 3 ≥ 0 := by
    have h2 : ((a + 2 * b) / (c + 2 * b) + (b + 2 * c) / (a + 2 * c) + (c + 2 * a) / (b + 2 * a) - 3) =
        ((a + 2 * b) * (a + 2 * c) * (b + 2 * a) + (b + 2 * c) * (c + 2 * b) * (b + 2 * a) + (c + 2 * a) * (c + 2 * b) * (a + 2 * c) - 3 * (c + 2 * b) * (a + 2 * c) * (b + 2 * a)) / ((c + 2 * b) * (a + 2 * c) * (b + 2 * a)) := by 
      field_simp
      ring
    rw [h2]
    have h3 : ((a + 2 * b) * (a + 2 * c) * (b + 2 * a) + (b + 2 * c) * (c + 2 * b) * (b + 2 * a) + (c + 2 * a) * (c + 2 * b) * (a + 2 * c) - 3 * (c + 2 * b) * (a + 2 * c) * (b + 2 * a)) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
    apply div_nonneg h3 
    positivity
  linarith