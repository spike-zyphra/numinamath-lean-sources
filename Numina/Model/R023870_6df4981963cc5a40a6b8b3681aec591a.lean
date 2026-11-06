import Mathlib

theorem inequalities_26579 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (b * c + a + 1) / (a ^ 2 + 1) + (c * a + b + 1) / (b ^ 2 + 1) +
    (a * b + c + 1) / (c ^ 2 + 1) ≤ 39 / 10 := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : a ^ 2 + 1 > 0 := by
    nlinarith
  have h3 : b ^ 2 + 1 > 0 := by
    nlinarith
  have h4 : c ^ 2 + 1 > 0 := by
    nlinarith
  have h5 : (b * c + a + 1) / (a ^ 2 + 1) + (c * a + b + 1) / (b ^ 2 + 1) + (a * b + c + 1) / (c ^ 2 + 1) - 39 / 10 ≤ 0 := by
    have h6 : (b * c + a + 1) / (a ^ 2 + 1) + (c * a + b + 1) / (b ^ 2 + 1) + (a * b + c + 1) / (c ^ 2 + 1) - 39 / 10 =
        (10 * ((b * c + a + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) + 10 * ((c * a + b + 1) * (a ^ 2 + 1) * (c ^ 2 + 1)) + 10 * ((a * b + c + 1) * (a ^ 2 + 1) * (b ^ 2 + 1)) - 39 * (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) / (10 * (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) := by
      field_simp
      ring
    rw [h6]
    have h7 : 10 * ((b * c + a + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) + 10 * ((c * a + b + 1) * (a ^ 2 + 1) * (c ^ 2 + 1)) + 10 * ((a * b + c + 1) * (a ^ 2 + 1) * (b ^ 2 + 1)) - 39 * (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) ≤ 0 := by
      have h8 : c = 1 - a - b := by linarith
      rw [h8]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - (1 - a - b)), sq_nonneg (a - (1 - a - b)), 
          sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg ((1 - a - b) - 1 / 3), 
          mul_pos ha hb, mul_pos hb (show 0 < (1 - a - b : ℝ) by nlinarith [h, hc]), mul_pos ha (show 0 < (1 - a - b : ℝ) by nlinarith [h, hc]), 
          sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (b * (1 - a - b) - (1 - a - b) * a), sq_nonneg ((1 - a - b) * a - a * b)]
    have h8 : (10 * ((b * c + a + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) + 10 * ((c * a + b + 1) * (a ^ 2 + 1) * (c ^ 2 + 1)) + 10 * ((a * b + c + 1) * (a ^ 2 + 1) * (b ^ 2 + 1)) - 39 * (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) / (10 * (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg h7 (by positivity)
    linarith
  linarith