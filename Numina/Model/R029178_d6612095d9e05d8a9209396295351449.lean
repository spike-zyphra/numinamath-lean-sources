import Mathlib

theorem inequalities_598922 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 4 ≤ a^2 / ((a + b) * (a + c)) + b^2 / ((b + c) * (b + a)) +
    c^2 / ((c + a) * (c + b)) := by
  have h1 : 0 < (a + b) * (a + c) := by positivity
  have h2 : 0 < (b + c) * (b + a) := by positivity
  have h3 : 0 < (c + a) * (c + b) := by positivity
  have h6 : a^2 / ((a + b) * (a + c)) + b^2 / ((b + c) * (b + a)) + c^2 / ((c + a) * (c + b)) - 3 / 4 ≥ 0 := by
    have h7 : 0 < (a + b) * (a + c) * (b + c) * (b + a) * (c + a) * (c + b) := by positivity
    have h8 : a^2 / ((a + b) * (a + c)) + b^2 / ((b + c) * (b + a)) + c^2 / ((c + a) * (c + b)) - 3 / 4 =
        (4 * a^2 * (b + c) * (b + a) * (c + a) * (c + b) +
          4 * b^2 * (a + c) * (a + b) * (c + a) * (c + b) +
          4 * c^2 * (a + b) * (a + c) * (b + c) * (b + a) - 3 * (a + b) * (a + c) * (b + c) * (b + a) * (c + a) * (c + b)) / (4 * (a + b) * (a + c) * (b + c) * (b + a) * (c + a) * (c + b)) := by
      field_simp
      ring
    rw [h8] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
    positivity
  linarith