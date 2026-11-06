import Mathlib

theorem inequalities_292715 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3/2 * (a^2 + b^2 + c^2) ≤ (a^3 + 5 * b^3)/(3 * a + b) + (b^3 + 5 * c^3)/(3 * b + c) +
    (c^3 + 5 * a^3)/(3 * c + a) := by
  have hb1 : 0 < 3 * a + b := by
    nlinarith
  have hb2 : 0 < 3 * b + c := by
    nlinarith
  have hb3 : 0 < 3 * c + a := by
    nlinarith
  have h1 : (a^3 + 5 * b^3) / (3 * a + b) + (b^3 + 5 * c^3) / (3 * b + c) + (c^3 + 5 * a^3) / (3 * c + a) ≥ 3 / 2 * (a^2 + b^2 + c^2) := by
    have h2 : (a^3 + 5 * b^3) / (3 * a + b) + (b^3 + 5 * c^3) / (3 * b + c) + (c^3 + 5 * a^3) / (3 * c + a) - 3/2 * (a^2 + b^2 + c^2) ≥ 0 := by
      have pos1 : 0 < (3 * a + b) * (3 * b + c) * (3 * c + a) := by positivity
      have h3 : (a^3 + 5 * b^3) / (3 * a + b) + (b^3 + 5 * c^3) / (3 * b + c) + (c^3 + 5 * a^3) / (3 * c + a) - 3/2 * (a^2 + b^2 + c^2) =
          ((a^3 + 5 * b^3) * (3 * b + c) * (3 * c + a) + (b^3 + 5 * c^3) * (3 * a + b) * (3 * c + a) + (c^3 + 5 * a^3) * (3 * a + b) * (3 * b + c) - 3/2 * (a^2 + b^2 + c^2) * (3 * a + b) * (3 * b + c) * (3 * c + a)) / ((3 * a + b) * (3 * b + c) * (3 * c + a)) := by
        field_simp
        ring
      rw [h3] at *
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
      all_goals positivity
    linarith
  linarith