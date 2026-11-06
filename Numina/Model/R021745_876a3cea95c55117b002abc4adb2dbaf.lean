import Mathlib
open Real

theorem inequalities_1820 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = 1) : a / (a + 1) + b / (b + 1) + c / (c + 1) ≤ 3 / 4 := by
  have h1 : 0 < a + 1 := by linarith
  have h2 : 0 < b + 1 := by linarith
  have h3 : 0 < c + 1 := by linarith
  have h4 : a / (a + 1) + b / (b + 1) + c / (c + 1) - 3 / 4 ≤ 0 := by
    have h5 : a / (a + 1) + b / (b + 1) + c / (c + 1) - 3 / 4 =
        (4 * a * (b + 1) * (c + 1) + 4 * b * (a + 1) * (c + 1) + 4 * c * (a + 1) * (b + 1) - 3 * (a + 1) * (b + 1) * (c + 1)) / (4 * (a + 1) * (b + 1) * (c + 1)) := by
      field_simp
      ring
    rw [h5]
    have h6 : 4 * a * (b + 1) * (c + 1) + 4 * b * (a + 1) * (c + 1) + 4 * c * (a + 1) * (b + 1) - 3 * (a + 1) * (b + 1) * (c + 1) ≤ 0 := by
      have h7 : c = 1 - a - b := by linarith
      rw [h7]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          mul_pos ha hb, mul_pos hb (show 0 < 1 - a - b by nlinarith), 
          mul_pos ha (show 0 < 1 - a - b by nlinarith), 
          sq_nonneg (a + b - (1 - a - b)), sq_nonneg (a - 1/2), sq_nonneg (b - 1/2), 
          sq_nonneg ((1 - a - b) - 1/2)]
    have h7 : 4 * (a + 1) * (b + 1) * (c + 1) > 0 := by
      positivity
    apply div_nonpos_of_nonpos_of_nonneg h6 (by positivity)
  linarith