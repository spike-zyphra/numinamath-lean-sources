import Mathlib

theorem inequalities_603204 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    5 ≤ 1 / a + 1 / b + 1 / c + 6 / (a + b + c) := by 
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : 0 < a + b + c := by
    positivity

  have h13 : 1 / a + 1 / b + 1 / c + 6 / (a + b + c) - 5 ≥ 0 := by 
    have h4 : 1 / a + 1 / b + 1 / c + 6 / (a + b + c) - 5 =
        ( (b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) + 6 * a * b * c - 5 * a * b * c * (a + b + c) ) ) / (a * b * c * (a + b + c)) := by
      field_simp
      ring 
    rw [h4] at *
    have h5 : a * b * c * (a + b + c) > 0 := by
      positivity
    have h6 : b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) + 6 * a * b * c - 5 * a * b * c * (a + b + c) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a + b + c - 3), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        habc]
    have h7 : (b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) + 6 * a * b * c - 5 * a * b * c * (a + b + c) ) ≥ 0 := h6
    have h8 : (b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) + 6 * a * b * c - 5 * a * b * c * (a + b + c) ) / (a * b * c * (a + b + c)) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith

  linarith