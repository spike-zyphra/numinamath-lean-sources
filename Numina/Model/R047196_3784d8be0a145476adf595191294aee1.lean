import Mathlib

theorem inequalities_179418 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + 3 * c) / (3 * a + 3 * b + 2 * c) +
    (a + 3 * b + c) / (3 * a + 2 * b + 3 * c) +
    (3 * a + b + c) / (2 * a + 3 * b + 3 * c) ≥ 15 / 8
  := by
  have h1 : 0 < (3 * a + 3 * b + 2 * c) := by positivity
  have h2 : 0 < (3 * a + 2 * b + 3 * c) := by positivity
  have h3 : 0 < (2 * a + 3 * b + 3 * c) := by positivity

  have h4 : (a + b + 3 * c) / (3 * a + 3 * b + 2 * c) +
      (a + 3 * b + c) / (3 * a + 2 * b + 3 * c) +
      (3 * a + b + c) / (2 * a + 3 * b + 3 * c) - 15 / 8 ≥ 0
    := by
    have h5 : 0 < 8 * (3 * a + 3 * b + 2 * c) * (3 * a + 2 * b + 3 * c) * (2 * a + 3 * b + 3 * c) := by positivity
    have h6 : (a + b + 3 * c) / (3 * a + 3 * b + 2 * c) +
        (a + 3 * b + c) / (3 * a + 2 * b + 3 * c) +
        (3 * a + b + c) / (2 * a + 3 * b + 3 * c) - 15 / 8 =
          (8 * (a + b + 3 * c) * (3 * a + 2 * b + 3 * c) * (2 * a + 3 * b + 3 * c) +
          8 * (a + 3 * b + c) * (3 * a + 3 * b + 2 * c) * (2 * a + 3 * b + 3 * c) +
          8 * (3 * a + b + c) * (3 * a + 3 * b + 2 * c) * (3 * a + 2 * b + 3 * c) -
          15 * (3 * a + 3 * b + 2 * c) * (3 * a + 2 * b + 3 * c) * (2 * a + 3 * b + 3 * c)) / (8 * (3 * a + 3 * b + 2 * c) * (3 * a + 2 * b + 3 * c) * (2 * a + 3 * b + 3 * c))
      := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
      sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      mul_pos (show 0 < a + b + c by linarith) (show 0 < a + b + c by linarith)]
    positivity
  linarith