import Mathlib

theorem inequalities_65277 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 + 3 / (a * b + b * c + c * a) ≥ 6 / (a + b + c) := by
  have h1 : 0 < a * b + b * c + c * a := by
    have h2 : 0 < a * b := by nlinarith
    have h3 : 0 < b * c := by nlinarith
    have h4 : 0 < c * a := by nlinarith
    linarith
  have h2 : 0 < a + b + c := by
    linarith
  have h4 : 1 + 3 / (a * b + b * c + c * a) - 6 / (a + b + c) ≥ 0 := by
    have h6 : 0 < (a * b + b * c + c * a) := h1
    have h7 : 0 < a + b + c := h2
    have h8 : (a * b + b * c + c * a) * (a + b + c) + 3 * (a + b + c) - 6 * (a * b + b * c + c * a) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              sq_nonneg (a + b + c - 3), sq_nonneg ((a * b + b * c + c * a) - 3),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h13 : 1 + 3 / (a * b + b * c + c * a) - 6 / (a + b + c) =
        ( (a * b + b * c + c * a) * (a + b + c) + 3 * (a + b + c) - 6 * (a * b + b * c + c * a) ) / ( (a * b + b * c + c * a) * (a + b + c) ) := by
      field_simp
      <;> ring
    rw [h13] at *
    apply div_nonneg
    linarith [h8]
    positivity
  linarith [h4]
  all_goals positivity