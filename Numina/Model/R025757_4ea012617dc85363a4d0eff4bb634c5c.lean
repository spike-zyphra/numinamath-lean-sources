import Mathlib

open Real

theorem algebra_262672 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : (a + c) * (b + d) = a * c + b * d) :
    a / b + b / c + c / d + d / a ≥ 8 := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * d := mul_pos hc hd
  have h4 : 0 < d * a := mul_pos hd ha
  have h5 : a / b + b / c + c / d + d / a - 8 ≥ 0 := by
    have h6 : 0 < a * b * c * d := by
      positivity
    have h5 : a / b + b / c + c / d + d / a - 8 ≥ 0 := by
      have h7 : a / b + b / c + c / d + d / a - 8 =
          (a ^ 2 * c * d + b ^ 2 * a * d + c ^ 2 * a * b + d ^ 2 * b * c - 8 * a * b * c * d) / (a * b * c * d) := by
        field_simp
        ring
      rw [h7] at *
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (a * d - b * c), sq_nonneg (a * c - b * d), sq_nonneg (b * a - c * d), sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a * b + c * d - (b * c + a * d)), sq_nonneg (a * d - b * c), sq_nonneg (a * (b + d) - c * (b + d)), sq_nonneg (b * a - c * d), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, h
      ]
      all_goals
        positivity
    linarith
  linarith