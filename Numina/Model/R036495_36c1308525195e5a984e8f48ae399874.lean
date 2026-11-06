import Mathlib

theorem inequalities_102589 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b / (a + b) + b * c / (b + c) + c * a / (c + a) ≤
    3 * (a * b + b * c + c * a) / (2 * (a + b + c)) := by
  have h1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have h2 : 0 < a + b := by linarith
  have h3 : 0 < b + c := by linarith
  have h4 : 0 < c + a := by linarith
  have h5 : 0 < 2 * (a + b + c) := by
    nlinarith
  have h6 : 0 < (a + b) * (b + c) * (c + a) * (2 * (a + b + c)) := by
    positivity
  have h7 : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) - 3 * (a * b + b * c + c * a) / (2 * (a + b + c)) ≤ 0 := by
    have h8 : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) - 3 * (a * b + b * c + c * a) / (2 * (a + b + c)) =
        ( 2 * (a + b + c) * (a * b * (b + c) * (c + a) ) + 2 * (a + b + c) * (b * c * (a + b) * (c + a) ) + 2 * (a + b + c) * (c * a * (a + b) * (b + c) ) - 3 * (a * b + b * c + c * a) * (a + b) * (b + c) * (c + a) ) / ( (a + b) * (b + c) * (c + a) * (2 * (a + b + c)) ) := by
      field_simp
      ring
    rw [h8]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Numerator ≤ 0
      nlinarith [ sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    · -- Denominator ≥ 0
      positivity
  linarith