import Mathlib

theorem inequalities_238934
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    ((2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) +
     (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) +
     (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2)) ≤ 8 := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc

  have h1' : 0 < 2 * a ^ 2 + (b + c) ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]

  have h2' : 0 < 2 * b ^ 2 + (c + a) ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]

  have h3' : 0 < 2 * c ^ 2 + (a + b) ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]

  have h4 : (2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) +
    (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) +
    (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) - 8 ≤ 0 := by

    have h5 : (2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) +
      (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) +
      (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) - 8 =
        ((2 * a + b + c) ^ 2 * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) +
        (a + 2 * b + c) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) +
        (a + b + 2 * c) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) - 8 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2)) / ((2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2)) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Numerator ≤ 0
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a * b by positivity) (show 0 < a * c by positivity),
        mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity),
        mul_pos (show 0 < a * c by positivity) (show 0 < b * c by positivity)]
    · -- Denominator ≥ 0
      positivity
  linarith