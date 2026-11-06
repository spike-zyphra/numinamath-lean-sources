import Mathlib

theorem inequalities_599970 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    (a / (a ^ 2 + b) + b / (a + b ^ 2)) ≤ 4 / 3 ∧
    (a / (a + b ^ 3) + b / (a ^ 3 + b)) ≤ 8 / 5 := by
  constructor
  · -- First part: prove a / (a ^ 2 + b) + b / (a + b ^ 2) ≤ 4 / 3
    have h1 : 0 < a ^ 2 + b := by
      nlinarith [h, sq_pos_of_pos ha]
    have h2 : 0 < a + b ^ 2 := by
      nlinarith [h, sq_pos_of_pos hb]
    have h3 : a / (a ^ 2 + b) + b / (a + b ^ 2) - 4 / 3 ≤ 0 := by
      have h4 : a / (a ^ 2 + b) + b / (a + b ^ 2) - 4 / 3 =
          (3 * a * (a + b ^ 2) + 3 * b * (a ^ 2 + b) - 4 * (a ^ 2 + b) * (a + b ^ 2)) / (3 * (a ^ 2 + b) * (a + b ^ 2)) := by
        field_simp
        <;> ring
      rw [h4] at *
      have h5 : 0 < 3 * (a ^ 2 + b) * (a + b ^ 2) := by
        positivity
      have h6 : 3 * a * (a + b ^ 2) + 3 * b * (a ^ 2 + b) - 4 * (a ^ 2 + b) * (a + b ^ 2) ≤ 0 := by
        have h7 : b = 1 - a := by linarith [h]
        rw [h7]
        nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2), 
          mul_pos ha (show 0 < (1 - a) by nlinarith [h, ha, hb]), 
          sq_nonneg (a * (a - 1 / 2)), sq_nonneg ((1 - a) * ((1 - a) - 1 / 2)), 
          mul_pos (show 0 < (1 - a) by nlinarith [h, ha, hb]) (show 0 < (1 - a) by nlinarith [h, ha, hb]), 
          mul_pos ha (show 0 < 1 - a by nlinarith [h, ha, hb]), 
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 1 - a by nlinarith)
        ]
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith [h6]
      · linarith [h5]
    linarith [h3]
  · -- Second part: prove a / (a + b ^ 3) + b / (a ^ 3 + b) ≤ 8 / 5
    have h1 : 0 < a + b ^ 3 := by
      nlinarith [h, sq_pos_of_pos hb, h]
    have h2 : 0 < a ^ 3 + b := by
      nlinarith [h, sq_pos_of_pos ha, h]
    have h3 : a / (a + b ^ 3) + b / (a ^ 3 + b) - 8 / 5 ≤ 0 := by
      have h4 : a / (a + b ^ 3) + b / (a ^ 3 + b) - 8 / 5 =
          (5 * a * (a ^ 3 + b) + 5 * b * (a + b ^ 3) - 8 * (a + b ^ 3) * (a ^ 3 + b)) / (5 * (a + b ^ 3) * (a ^ 3 + b)) := by
        field_simp
        <;> ring
      rw [h4] at *
      have h5 : 0 < 5 * (a + b ^ 3) * (a ^ 3 + b) := by
        positivity
      have h6 : 5 * a * (a ^ 3 + b) + 5 * b * (a + b ^ 3) - 8 * (a + b ^ 3) * (a ^ 3 + b) ≤ 0 := by
        have h7 : b = 1 - a := by linarith [h]
        rw [h7]
        nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2), 
          mul_pos ha (show 0 < (1 - a) by nlinarith [h, ha, hb]), 
          sq_nonneg (a * (a - 1 / 2)), sq_nonneg ((1 - a) * ((1 - a) - 1 / 2)), 
          mul_pos (show 0 < (1 - a) by nlinarith [h, ha, hb]) (show 0 < (1 - a) by nlinarith [h, ha, hb]), 
          sq_nonneg (a * b), sq_nonneg ((a - b) * (a - b)), 
          mul_pos ha (show 0 < 1 - a by nlinarith [h, ha, hb])
        ]
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith [h6]
      · linarith [h5]
    linarith [h3]