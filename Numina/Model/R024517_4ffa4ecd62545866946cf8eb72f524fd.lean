import Mathlib

theorem inequalities_102540 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 2 ≤ a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) := by
  have h4 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) ≥ (a + b + c) / 2 := by
    have hb_pos : 0 < b + c := by linarith
    have hc_pos : 0 < c + a := by linarith
    have ha_pos : 0 < a + b := by linarith
    have h5 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - (a + b + c) / 2 ≥ 0 := by
      have h6 : 0 < (b + c) * (c + a) * (a + b) := by positivity
      have h7 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - (a + b + c) / 2 =
          (2 * a^2 * (c + a) * (a + b) + 2 * b^2 * (b + c) * (a + b) + 2 * c^2 * (b + c) * (c + a) - (a + b + c) * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by
        field_simp
        ring
      rw [h7] at *
      apply div_nonneg
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
                sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
                sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
                mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith), 
                mul_pos (show 0 < a * c by nlinarith) (show 0 < b by linarith), 
                mul_pos (show 0 < b * c by nlinarith) (show 0 < a by linarith)
      ]
      all_goals positivity
    linarith
  have h5 : (a + b + c) / 2 ≥ 3 / 2 := by
    have h6 : a + b + c ≥ 3 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc
        ]
    linarith
  linarith [h4, h5]