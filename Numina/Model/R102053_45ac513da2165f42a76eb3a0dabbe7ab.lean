import Mathlib

theorem inequalities_205793 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) ≤ 1 := by

  have h2 : 0 < (1 + a + b) * (1 + b + c) * (1 + c + a) := by positivity
  have h3 : 1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) - 1 ≤ 0 := by
    have h4 : (1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) - 1) =
        ((1 + b + c) * (1 + c + a) + (1 + a + b) * (1 + c + a) + (1 + a + b) * (1 + b + c) - (1 + a + b) * (1 + b + c) * (1 + c + a)) / ((1 + a + b) * (1 + b + c) * (1 + c + a)) := by
      field_simp
      ring
      <;> field_simp <;> ring
    rw [h4]
    apply div_nonpos_of_nonpos_of_nonneg
    -- The numerator is non-positive, and denominators are positive. So forming a total. Therefore forming a numerator non-positive.
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b * c - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]

    -- The denominator is non-negative.
    positivity

  linarith [h3]