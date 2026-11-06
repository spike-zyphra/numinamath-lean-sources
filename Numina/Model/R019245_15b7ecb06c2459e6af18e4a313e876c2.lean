import Mathlib

theorem inequalities_603770 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 + b^2 + c^2 ≥ c * (a^2 + b^2) / (a + b) + b * (c^2 + a^2) / (c + a) +
      a * (b^2 + c^2) / (b + c) := by
  have h1 : 0 < a + b := by
    linarith
  have h2 : 0 < c + a := by
    linarith
  have h3 : 0 < b + c := by
    linarith
  have h4 : c * (a^2 + b^2) / (a + b) + b * (c^2 + a^2) / (c + a) + a * (b^2 + c^2) / (b + c) ≤ a^2 + b^2 + c^2 := by
    have h5 : 0 < (a + b) * (c + a) * (b + c) := by positivity
    have h6 : c * (a^2 + b^2) / (a + b) + b * (c^2 + a^2) / (c + a) + a * (b^2 + c^2) / (b + c) - (a^2 + b^2 + c^2) ≤ 0 := by
      have h7 : c * (a^2 + b^2) / (a + b) + b * (c^2 + a^2) / (c + a) + a * (b^2 + c^2) / (b + c) - (a^2 + b^2 + c^2) =
          (c * (a^2 + b^2) * (c + a) * (b + c) + b * (c^2 + a^2) * (a + b) * (b + c) + a * (b^2 + c^2) * (a + b) * (c + a) - (a^2 + b^2 + c^2) * (a + b) * (c + a) * (b + c)) / ((a + b) * (c + a) * (b + c)) := by
        field_simp
        ring
      rw [h7]
      apply div_nonpos_of_nonpos_of_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      all_goals positivity
    linarith
  linarith [h4]