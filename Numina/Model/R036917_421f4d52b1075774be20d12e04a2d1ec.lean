import Mathlib

theorem algebra_131799 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : (a + c) * (b + d) = a * c + b * d) :
    a / b + b / c + c / d + d / a ≥ 8 := by
  have h1 : 0 < a * b * c * d := by
    positivity
  have hb0 : 0 < b := hb
  have ha0 : 0 < a := ha
  have hc0 : 0 < c := hc
  have hd0 : 0 < d := hd
  have hb6 : a / b + b / c + c / d + d / a - 8 ≥ 0 := by
    have h7 : a / b + b / c + c / d + d / a - 8 = (a ^ 2 * c * d + b ^ 2 * a * d + c ^ 2 * b * a + d ^ 2 * b * c - 8 * a * b * c * d) / (a * b * c * d) := by
      field_simp [hb0.ne', ha0.ne', hc0.ne', hd0.ne']
      ring
    rw [h7]
    have hb7 : a ^ 2 * c * d + b ^ 2 * a * d + c ^ 2 * b * a + d ^ 2 * b * c - 8 * a * b * c * d ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * d), sq_nonneg (c * d - d * a), sq_nonneg (d * a - a * b),
          sq_nonneg (a * d - b * c), sq_nonneg (a * b - c * d), sq_nonneg (a * c - b * d), sq_nonneg (a - c), sq_nonneg (b - d),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
    apply div_nonneg
    .
      linarith
    all_goals positivity
  linarith