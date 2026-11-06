import Mathlib

theorem inequalities_597631
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    6 ≤ ((a + b) ^ 2 / (c ^ 2 + a * b) + (b + c) ^ 2 / (a ^ 2 + b * c) +
        (c + a) ^ 2 / (b ^ 2 + a * c)) := by

  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a * c := mul_pos ha hc
  have h3 : 0 < b * c := mul_pos hb hc
  have h4 : 0 < c ^ 2 + a * b := by nlinarith [sq_nonneg c, h1]
  have h5 : 0 < a ^ 2 + b * c := by nlinarith [sq_nonneg a, h3]
  have h6 : 0 < b ^ 2 + a * c := by nlinarith [sq_nonneg b, h2]
  have h7 : (a + b) ^ 2 / (c ^ 2 + a * b) + (b + c) ^ 2 / (a ^ 2 + b * c) + (c + a) ^ 2 / (b ^ 2 + a * c) - 6 ≥ 0 := by
    have h8 : (a + b) ^ 2 / (c ^ 2 + a * b) + (b + c) ^ 2 / (a ^ 2 + b * c) + (c + a) ^ 2 / (b ^ 2 + a * c) - 6 =
        ((a + b) ^ 2 * (a ^ 2 + b * c) * (b ^ 2 + a * c) + (b + c) ^ 2 * (c ^ 2 + a * b) * (b ^ 2 + a * c) + (c + a) ^ 2 * (c ^ 2 + a * b) * (a ^ 2 + b * c) - 6 * (c ^ 2 + a * b) * (a ^ 2 + b * c) * (b ^ 2 + a * c)) / ((c ^ 2 + a * b) * (a ^ 2 + b * c) * (b ^ 2 + a * c)) := by
      field_simp
      ring
    rw [h8]
    have h9 : ((a + b) ^ 2 * (a ^ 2 + b * c) * (b ^ 2 + a * c) + (b + c) ^ 2 * (c ^ 2 + a * b) * (b ^ 2 + a * c) + (c + a) ^ 2 * (c ^ 2 + a * b) * (a ^ 2 + b * c) - 6 * (c ^ 2 + a * b) * (a ^ 2 + b * c) * (b ^ 2 + a * c)) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)
        ]
    apply div_nonneg
    · linarith
    · positivity
  linarith