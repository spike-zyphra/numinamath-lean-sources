import Mathlib

theorem inequalities_157700 (a b c : ℝ) (h : a > b ∧ b > c) :
    1 / (a - b) + 1 / (b - c) + 4 / (c - a) ≥ 0 := by

  have h1 : a - b > 0 := by
    linarith [h.1]

  have h2 : b - c > 0 := by
    linarith [h.2]

  have h3 : c - a < 0 := by
    linarith [h.1, h.2]

  have h4 : a - c > 0 := by
    linarith [h.1, h.2]

  have h5 : (b - c) * (a - c) + (a - b) * (a - c) - 4 * ((a - b) * (b - c)) ≥ 0 := by
    nlinarith [sq_nonneg (a - 2 * b + c), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a - b), 
              mul_pos (sub_pos.mpr h.1) (sub_pos.mpr h.2)]

  have h6 : 1 / (a - b) + 1 / (b - c) + 4 / (c - a) = 
          ((b - c) * (a - c) + (a - b) * (a - c) - 4 * ((a - b) * (b - c))) / ((a - b) * (b - c) * (a - c)) := by
    field_simp [(show a - b ≠ 0 by linarith), (show b - c ≠ 0 by linarith), 
                (show c - a ≠ 0 by 
                  nlinarith 
                )
              ]
    ring

  rw [h6]

  have h_pos1 : (a - b) * (b - c) * (a - c) > 0 := by
    have hb : a - b > 0 := h1
    have hc : b - c > 0 := h2
    have ha : a - c > 0 := h4
    positivity

  apply div_nonneg 
  linarith [h5]
  all_goals linarith [h_pos1]