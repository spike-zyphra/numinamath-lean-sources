import Mathlib

theorem inequalities_33122 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / 2 ≤ a / (c + 5 * b) + b / (a + 5 * c) + c / (b + 5 * a) := by

  have h1 : 0 < c + 5 * b := by nlinarith
  have h2 : 0 < a + 5 * c := by nlinarith
  have h3 : 0 < b + 5 * a := by nlinarith

  have h4 : a / (c + 5 * b) + b / (a + 5 * c) + c / (b + 5 * a) - 1 / 2 ≥ 0 := by

    have pos1 : 0 < c + 5 * b := by nlinarith
    have pos2 : 0 < a + 5 * c := by nlinarith
    have pos3 : 0 < b + 5 * a := by nlinarith

    have h5 : a / (c + 5 * b) + b / (a + 5 * c) + c / (b + 5 * a) - 1 / 2 =
          (2 * (a * (a + 5 * c) * (b + 5 * a) +
                b * (b + 5 * a) * (c + 5 * b) +
                c * (c + 5 * b) * (a + 5 * c)) -
           (c + 5 * b) * (a + 5 * c) * (b + 5 * a)) / (2 * (c + 5 * b) * (a + 5 * c) * (b + 5 * a)) := by
      field_simp
      ring

    rw [h5]

    have h6 : 2 * (a * (a + 5 * c) * (b + 5 * a) + b * (b + 5 * a) * (c + 5 * b) + c * (c + 5 * b) * (a + 5 * c)) - (c + 5 * b) * (a + 5 * c) * (b + 5 * a) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

    have h7 : 0 ≤ 2 * (c + 5 * b) * (a + 5 * c) * (b + 5 * a) := by positivity
    apply div_nonneg
    linarith
    positivity

  linarith