import Mathlib

theorem inequalities_605087 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = 1) :
    (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) ≥ 69 / 4 := by
  have h1 : 0 < (1 + a) * (1 + b) * (1 + c) := by
    positivity
  have h2 : (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) - 69 / 4 ≥ 0 := by
    have pos1 : 0 < (1 + a) := by
      nlinarith
    have pos2 : 0 < (1 + b) := by
      nlinarith
    have pos3 : 0 < (1 + c) := by
      nlinarith
    have pos4 : 0 < (1 + a) * (1 + b) * (1 + c) := by
      positivity
    have h3 : (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) - 69 / 4 =
          (4 * ((7 + 2 * b) * (1 + b) * (1 + c) + (7 + 2 * c) * (1 + a) * (1 + c) + (7 + 2 * a) * (1 + a) * (1 + b)) - 69 * ((1 + a) * (1 + b) * (1 + c))) / (4 * ( (1 + a) * (1 + b) * (1 + c)) ) := by 
          field_simp
          ring
    rw [h3] at *
    apply div_nonneg
    have h4 : 4 * ((7 + 2 * b) * (1 + b) * (1 + c) + (7 + 2 * c) * (1 + a) * (1 + c) + (7 + 2 * a) * (1 + a) * (1 + b)) - 69 * ((1 + a) * (1 + b) * (1 + c)) ≥ 0 := by
      have h_sum : c = 1 - a - b := by linarith 
      rw [h_sum]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (a * (1 - a - b) - b * (1 - a - b)), 
          mul_pos ha hb, mul_pos hb (show 0 < (1 - a - b) by nlinarith), 
          mul_pos ha (show 0 < (1 - a - b) by nlinarith)
        ]
    linarith
    all_goals
      positivity
  linarith