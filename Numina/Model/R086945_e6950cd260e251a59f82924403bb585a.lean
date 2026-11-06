import Mathlib

open Real Set

theorem inequalities_308819 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 108) :
    18 ≤ a * b / c + b * c / a + c * a / b := by
  have h1 : a * b / c + b * c / a + c * a / b ≥ 18 := by
    have pos1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
    have h2 : a * b / c + b * c / a + c * a / b - 18 ≥ 0 := by
      have h3 : a * b / c + b * c / a + c * a / b - 18 = (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 - 18 * a * b * c) / (a * b * c) := by
        field_simp
        ring
      rw [h3]
      have h4 : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ 18 * a * b * c := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h6 : a * b * c > 0 := mul_pos (mul_pos ha hb) hc
      apply div_nonneg
      linarith [show a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ 18 * a * b * c by linarith]
      positivity
    linarith
  linarith [h1]