import Mathlib


theorem inequalities_60169 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 3) :
    3 / 8 ≥ 1 / (4 + (a + b)^2) + 1 / (4 + (b + c)^2) + 1 / (4 + (c + a)^2) := by
  have h1 : 0 < a * b := by nlinarith
  have h2 : 0 < b * c := by nlinarith
  have h3 : 0 < c * a := by nlinarith
  have h4 : 0 < 4 + (a + b) ^ 2 := by nlinarith
  have h5 : 0 < 4 + (b + c) ^ 2 := by nlinarith
  have h6 : 0 < 4 + (c + a) ^ 2 := by nlinarith
  have h7 : 3 / 8 - (1 / (4 + (a + b) ^ 2) + 1 / (4 + (b + c) ^ 2) + 1 / (4 + (c + a) ^ 2) ) ≥ 0 := by
    have h8 : 0 < (4 + (a + b) ^ 2) * (4 + (b + c) ^ 2) * (4 + (c + a) ^ 2) := by positivity
    have h9 : 3 / 8 - (1 / (4 + (a + b) ^ 2) + 1 / (4 + (b + c) ^ 2) + 1 / (4 + (c + a) ^ 2)) =
        ( (3 * (4 + (a + b) ^ 2) * (4 + (b + c) ^ 2) * (4 + (c + a) ^ 2) - 8 * ( (4 + (b + c) ^ 2) * (4 + (c + a) ^ 2) + (4 + (a + b) ^ 2) * (4 + (c + a) ^ 2) + (4 + (a + b) ^ 2) * (4 + (b + c) ^ 2) ) ) ) / (8 * (4 + (a + b) ^ 2) * (4 + (b + c) ^ 2) * (4 + (c + a) ^ 2) ) := by
      field_simp
      ring
    rw [h9]
    have h10 : 3 * (4 + (a + b) ^ 2) * (4 + (b + c) ^ 2) * (4 + (c + a) ^ 2) - 8 * ( (4 + (b + c) ^ 2) * (4 + (c + a) ^ 2) + (4 + (a + b) ^ 2) * (4 + (c + a) ^ 2) + (4 + (a + b) ^ 2) * (4 + (b + c) ^ 2) ) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * b + b * c + c * a - 3), sq_nonneg (a * b * c - 1),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    apply div_nonneg
    · linarith
    · positivity
  linarith [h7]