import Mathlib

theorem inequalities_146907 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (1 / (a * b) + 1 / (a * c) + 1 / (a * d) + 1 / (b * c) + 1 / (b * d) + 1 / (c * d)) ≤
    3 / 8 * ((1 / a) + (1 / b) + (1 / c) + (1 / d))^2 := by
  have h7 : (1 / (a * b) + 1 / (a * c) + 1 / (a * d) + 1 / (b * c) + 1 / (b * d) + 1 / (c * d)) =
          (1 / a * (1 / b) + 1 / a * (1 / c) + 1 / a * (1 / d) + (1 / b) * (1 / c) + (1 / b) * (1 / d) + (1 / c) * (1 / d)) := by
    field_simp
    <;> ring
  rw [h7]
  have h8 : (1 / a) + (1 / b) + (1 / c) + (1 / d) = (1 / a) + (1 / b) + (1 / c) + (1 / d) := by rfl
  rw [h8]
  have h9 : (1 / a * (1 / b) + 1 / a * (1 / c) + 1 / a * (1 / d) + (1 / b) * (1 / c) + (1 / b) * (1 / d) + (1 / c) * (1 / d)) ≤ 3 / 8 * ((1 / a) + (1 / b) + (1 / c) + (1 / d))^2 := by
    nlinarith [sq_nonneg ((1 / a) - (1 / b)), sq_nonneg ((1 / a) - (1 / c)), sq_nonneg ((1 / a) - (1 / d)), sq_nonneg ((1 / b) - (1 / c)), sq_nonneg ((1 / b) - (1 / d)), sq_nonneg ((1 / c) - (1 / d)), 
          sq_nonneg ((1 / a) + (1 / b) + (1 / c) + (1 / d)), 
          mul_pos (show 0 < 1 / a by positivity) (show 0 < 1 / b by positivity), 
          mul_pos (show 0 < 1 / a by positivity) (show 0 < 1 / c by positivity), 
          mul_pos (show 0 < 1 / a by positivity) (show 0 < 1 / d by positivity), 
          mul_pos (show 0 < 1 / b by positivity) (show 0 < 1 / c by positivity), 
          mul_pos (show 0 < 1 / b by positivity) (show 0 < 1 / d by positivity), 
          mul_pos (show 0 < 1 / c by positivity) (show 0 < 1 / d by positivity)
        ]
  linarith [h9]