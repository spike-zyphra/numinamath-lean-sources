import Mathlib

theorem inequalities_46296 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
     (2 * b + c + a)^2 / (2 * b^2 + (c + a)^2) +
     (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2) ≤ 8) := by
  have h1 : 0 < 2 * a ^ 2 + (b + c) ^ 2 := by
    nlinarith [ha, hb, hc]

  have h2 : 0 < 2 * b ^ 2 + (c + a) ^ 2 := by
    nlinarith [ha, hb, hc]

  have h3 : 0 < 2 * c ^ 2 + (a + b) ^ 2 := by
    nlinarith [ha, hb, hc]

  have h4 : (2 * a + b + c) ^ 2 / (2 * a^ 2 + (b + c) ^ 2) + (2 * b + c + a) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (2 * c + a + b) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) - 8 ≤ 0 := by
    have h5 : 0 < (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) := by positivity
    have h6 : (2 * a + b + c) ^ 2 / (2 * a^ 2 + (b + c) ^ 2) + (2 * b + c + a) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (2 * c + a + b) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) - 8 =
        ((2 * a + b + c) ^ 2 * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) +
        (2 * b + c + a) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) +
        (2 * c + a + b) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) - 8 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2)) / ((2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2)) := by
      field_simp
      <;> ring
    rw [h6]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    · positivity

  linarith
  all_goals
    try { linarith }
    try { positivity }