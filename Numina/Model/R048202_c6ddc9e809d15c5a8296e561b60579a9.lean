import Mathlib

theorem inequalities_302594 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 3 / (a ^ 2 + a * b + b ^ 2) + b ^ 3 / (b ^ 2 + b * c + c ^ 2) +
     c ^ 3 / (c ^ 2 + c * a + a ^ 2)) ≥ (a + b + c) / 3 := by

  have h1 : a ^ 3 / (a ^ 2 + a * b + b ^ 2) ≥ (2 * a - b) / 3 := by
    have pos1 : 0 < a ^ 2 + a * b + b ^ 2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), mul_pos ha hb, sq_nonneg (a - b)]

  have h2 : b ^ 3 / (b ^ 2 + b * c + c ^ 2) ≥ (2 * b - c) / 3 := by
    have pos2 : 0 < b ^ 2 + b * c + c ^ 2 := by
      nlinarith [sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos hb hc]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), mul_pos hb hc, sq_nonneg (b - c)]

  have h3 : c ^ 3 / (c ^ 2 + c * a + a ^ 2) ≥ (2 * c - a) / 3 := by
    have pos3 : 0 < c ^ 2 + c * a + a ^ 2 := by
      nlinarith [sq_pos_of_pos hc, sq_pos_of_pos ha, mul_pos hc ha]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c * (c - a)), sq_nonneg (a * (c - a)), mul_pos hc ha, sq_nonneg (c - a)]

  linarith [h1, h2, h3]