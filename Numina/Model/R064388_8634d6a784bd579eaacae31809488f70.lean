import Mathlib

theorem inequalities_601386 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by

  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * a := mul_pos hc ha
  have h4 : 0 < b + c := by linarith
  have h5 : 0 < c + a := by linarith
  have h6 : 0 < a + b := by linarith

  have h7 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h9 : (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2) =
      (2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by
      field_simp
      ring

    rw [h9]

    have h10 : 0 < 2 * (b + c) * (c + a) * (a + b) := by positivity

    have h11 : 2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos hb hc, mul_pos hc ha]

    apply div_nonneg
    linarith
    positivity

  linarith