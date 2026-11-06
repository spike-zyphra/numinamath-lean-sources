import Mathlib

theorem inequalities_129499 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 - b * c) / (2 * a^2 + b * c) + (b^2 - c * a) / (2 * b^2 + c * a) +
    (c^2 - a * b) / (2 * c^2 + a * b) ≤ 0 := by
  have h1 : 0 < 2 * a^2 + b * c := by positivity
  have h2 : 0 < 2 * b^2 + c * a := by positivity
  have h3 : 0 < 2 * c^2 + a * b := by positivity
  have h4 : (a^2 - b * c) / (2 * a^2 + b * c) + (b^2 - c * a) / (2 * b^2 + c * a) + (c^2 - a * b) / (2 * c^2 + a * b) =
      ((a^2 - b * c) * (2 * b^2 + c * a) * (2 * c^2 + a * b) + (b^2 - c * a) * (2 * a^2 + b * c) * (2 * c^2 + a * b) + (c^2 - a * b) * (2 * a^2 + b * c) * (2 * b^2 + c * a)) / ((2 * a^2 + b * c) * (2 * b^2 + c * a) * (2 * c^2 + a * b)) := by
    field_simp [h1, h2, h3]
    ring
  rw [h4]
  apply div_nonpos_of_nonpos_of_nonneg
  · 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
  · 
    positivity