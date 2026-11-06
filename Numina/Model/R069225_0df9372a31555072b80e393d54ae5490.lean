import Mathlib
open Real

theorem inequalities_8674 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (c + 5 * b) + b / (a + 5 * c) + c / (b + 5 * a) ≥ 1 / 2 := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc

  have h4 : 0 < a + 5 * b := by nlinarith [h1, h2]

  have h5 : 0 < b + 5 * c := by nlinarith [h2, h3]

  have h6 : 0 < c + 5 * a := by nlinarith [h3, h1]

  have h7 : a / (c + 5 * b) + b / (a + 5 * c) + c / (b + 5 * a) - 1 / 2 ≥ 0 := by
    have h3000 : (a / (c + 5 * b) + b / (a + 5 * c) + c / (b + 5 * a) - 1 / 2) =
        (2 * a * (a + 5 * c) * (b + 5 * a) + 2 * b * (c + 5 * b) * (b + 5 * a) + 2 * c * (c + 5 * b) * (a + 5 * c) - (c + 5 * b) * (a + 5 * c) * (b + 5 * a)) / (2 * (c + 5 * b) * (a + 5 * c) * (b + 5 * a)) := by
      field_simp
      ring
    rw [h3000]
    have h5000 : 2 * (c + 5 * b) * (a + 5 * c) * (b + 5 * a) > 0 := by
      positivity

    have h5001 : (2 * a * (a + 5 * c) * (b + 5 * a) + 2 * b * (c + 5 * b) * (b + 5 * a) + 2 * c * (c + 5 * b) * (a + 5 * c) - (c + 5 * b) * (a + 5 * c) * (b + 5 * a)) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)),
          sq_nonneg (a - b + b - c), sq_nonneg (a - c + c - b), sq_nonneg (b - c + c - a),
          sq_nonneg (2 * a - b), sq_nonneg (2 * b - c), sq_nonneg (2 * c - a),
          mul_pos h1 h2, mul_pos h2 h3, mul_pos h3 h1]

    apply div_nonneg
    linarith
    all_goals nlinarith

  linarith