import Mathlib

open Real

theorem inequalities_597082 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 4 ≤ a * b / ((b + c) * (c + a)) + b * c / ((c + a) * (a + b)) +
    c * a / ((a + b) * (b + c)) := by 
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * a := mul_pos hc ha
  have h4 : 0 < (b + c) * (c + a) := mul_pos (show 0 < b + c by linarith) (show 0 < c + a by linarith)
  have h5 : 0 < (c + a) * (a + b) := mul_pos (show 0 < c + a by linarith) (show 0 < a + b by linarith)
  have h6 : 0 < (a + b) * (b + c) := mul_pos (show 0 < a + b by linarith) (show 0 < b + c by linarith)

  have h7 : a * b / ((b + c) * (c + a)) + b * c / ((c + a) * (a + b)) + c * a / ((a + b) * (b + c)) - 3 / 4 ≥ 0 := by
    have h8 : (a + b) * (b + c) * (c + a) > 0 := by positivity
    have h9 : a * b / ((b + c) * (c + a)) + b * c / ((c + a) * (a + b)) + c * a / ((a + b) * (b + c)) - 3 / 4 =
        (a * b * (a + b) + b * c * (b + c) + c * a * (c + a) - 3 / 4 * (a + b) * (b + c) * (c + a)) / ((a + b) * (b + c) * (c + a)) := by
      field_simp
      ring
    rw [h9]
    apply div_nonneg
    · -- Prove numerator is non-negative
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
    · -- Prove denominator is non-negative
      positivity

  linarith