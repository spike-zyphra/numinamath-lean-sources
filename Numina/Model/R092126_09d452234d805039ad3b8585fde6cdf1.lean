import Mathlib

theorem inequalities_42005 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    c / (a + 2 * b) + a / (b + 2 * c) + b / (c + 2 * a) ≥ 1 := by
        have h₁ : 0 < a + 2 * b := by linarith
        have h₂ : 0 < b + 2 * c := by linarith
        have h₃ : 0 < c + 2 * a := by linarith
        have h4 : c / (a + 2 * b) + a / (b + 2 * c) + b / (c + 2 * a) - (1 : ℝ) ≥ 0 := by
            have h5 : c / (a + 2 * b) + a / (b + 2 * c) + b / (c + 2 * a) - (1 : ℝ) =
                (c * (b + 2 * c) * (c + 2 * a) + a * (a + 2 * b) * (c + 2 * a) + b * (a + 2 * b) * (b + 2 * c) - (a + 2 * b) * (b + 2 * c) * (c + 2 * a)) /
                ((a + 2 * b) * (b + 2 * c) * (c + 2 * a)) := by
                field_simp
                ring
            rw [h5]
            have h6 : (a + 2 * b) * (b + 2 * c) * (c + 2 * a) > 0 := by positivity
            apply div_nonneg
            nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                      sq_nonneg (a - 2 * b), sq_nonneg (b - 2 * c), sq_nonneg (c - 2 * a),
                      ha, hb, hc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
            all_goals positivity
        linarith