import Mathlib

theorem inequalities_195765 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    c / a + a / (b + c) + b / c ≥ 2 := by
  have h1 : c / a + a / (b + c) + b / c - 2 ≥ 0 := by
    have h2 : c / a + a / (b + c) + b / c - 2 =
        (c * (b + c) * c + a * a * c + b * a * (b + c) - 2 * a * (b + c) * c) / (a * (b + c) * c) := by
      field_simp
      ring
    rw [h2]
    have h7 : 0 < a * (b + c) * c := by
      positivity
    have h8 : c * (b + c) * c + a * a * c + b * a * (b + c) - 2 * a * (b + c) * c ≥ 0 := by
      nlinarith [sq_nonneg (a - (b + c)), sq_nonneg (a * (b + c) - c * a), sq_nonneg (a * c - b * c), sq_nonneg (a * b - c * b), sq_nonneg (c - b), sq_nonneg (a * c - c * (b + c)), sq_nonneg (a * b - a * c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_self_nonneg (a - c), mul_self_nonneg (a - b), mul_self_nonneg (b - c)]
    apply div_nonneg
    linarith [h8]
    all_goals try positivity
    all_goals try nlinarith [h8]
    all_goals try linarith [h7]
    all_goals try tauto
  linarith [h1]