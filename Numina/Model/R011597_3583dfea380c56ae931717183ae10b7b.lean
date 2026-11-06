import Mathlib

theorem inequalities_37992 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 * b ^ 2 / (a + b) + b ^ 2 * c ^ 2 / (b + c) + c ^ 2 * a ^ 2 / (c + a)) ≤
    (a ^ 3 + b ^ 3 + c ^ 3) / 2 := by
  have pos1 : 0 < a + b := by linarith
  have pos2 : 0 < b + c := by linarith
  have pos3 : 0 < c + a := by linarith
  have h1 : 0 < (a + b) * (b + c) * (c + a) := by positivity
  have h2 : a ^ 2 * b ^ 2 / (a + b) + b ^ 2 * c ^ 2 / (b + c) + c ^ 2 * a ^ 2 / (c + a) - (a ^ 3 + b ^ 3 + c ^ 3) / 2 ≤ 0 := by
    have h3 : 0 < (a + b) * (b + c) * (c + a) := by positivity
    have h4 : a ^ 2 * b ^ 2 / (a + b) + b ^ 2 * c ^ 2 / (b + c) + c ^ 2 * a ^ 2 / (c + a) - (a ^ 3 + b ^ 3 + c ^ 3) / 2 =
        (2 * (a ^ 2 * b ^ 2 * (b + c) * (c + a) + b ^ 2 * c ^ 2 * (a + b) * (c + a) + c ^ 2 * a ^ 2 * (a + b) * (b + c)) - (a ^ 3 + b ^ 3 + c ^ 3) * (a + b) * (b + c) * (c + a)) / (2 * (a + b) * (b + c) * (c + a)) := by
      field_simp
      ring
    rw [h4]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show numerator is ≤ 0
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    · -- Show denominator is ≥ 0
      positivity
  linarith