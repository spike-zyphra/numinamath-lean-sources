import Mathlib

theorem inequalities_603384
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 1 / (a + b + c) ^ 2 ≥
    7 / 25 * ((1 / a + 1 / b + 1 / c + 1 / (a + b + c)) ^ 2) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : a ≠ 0 := by linarith
  have h3 : b ≠ 0 := by linarith
  have h4 : c ≠ 0 := by linarith
  have h5 : a + b + c ≠ 0 := by
    positivity
  have h6 : a ^ 2 > 0 := by positivity
  have h7 : b ^ 2 > 0 := by positivity
  have h8 : c ^ 2 > 0 := by positivity
  have h9 : (a + b + c) ^ 2 > 0 := by positivity
  suffices 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 1 / (a + b + c) ^ 2 - 7 / 25 * ((1 / a + 1 / b + 1 / c + 1 / (a + b + c)) ^ 2) ≥ 0 by linarith
  have h10 : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 1 / (a + b + c) ^ 2 - 7 / 25 * ((1 / a + 1 / b + 1 / c + 1 / (a + b + c)) ^ 2) =
      (b^2 * c^2 * (a + b + c)^2 + a^2 * c^2 * (a + b + c)^2 + a^2 * b^2 * (a + b + c)^2 + a^2 * b^2 * c^2 - 7 / 25 * (b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) + a * b * c)^2 ) / (a^2 * b^2 * c^2 * (a + b + c)^2) := by
    field_simp
    ring
  rw [h10]
  have pos2 : 0 < a^2 * b^2 * c^2 * (a + b + c) ^ 2 := by positivity
  apply div_nonneg
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      mul_pos (show 0 < a + b + c by positivity) (show 0 < a * b * c by positivity) ]
  all_goals positivity