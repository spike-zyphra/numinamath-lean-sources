import Mathlib

theorem inequalities_92574 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    1 ≤ 1 / (1 + 2 * a * b) + 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) := by
  have h₁ : 0 < a * b := mul_pos ha hb
  have h₂ : 0 < b * c := mul_pos hb hc
  have h₃ : 0 < c * a := mul_pos hc ha
  have pos1 : 0 < 1 + 2 * a * b := by
    nlinarith [h₁, sq_pos_of_pos ha, sq_pos_of_pos hb]
  have pos2 : 0 < 1 + 2 * b * c := by
    nlinarith [h₂, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have pos3 : 0 < 1 + 2 * c * a := by
    nlinarith [h₃, sq_pos_of_pos hc, sq_pos_of_pos ha]

  have h4 : 1 / (1 + 2 * a * b) + 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) - 1 ≥ 0 := by 
    have h9 : (1 / (1 + 2 * a * b) + 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) - 1 ) = ( (1 + 2 * b * c) * (1 + 2 * c * a) + (1 + 2 * a * b) * (1 + 2 * c * a) + (1 + 2 * a * b) * (1 + 2 * b * c) - (1 + 2 * a * b) * (1 + 2 * b * c) * (1 + 2 * c * a) ) / ((1 + 2 * a * b) * (1 + 2 * b * c) * (1 + 2 * c * a)) := by
      field_simp
      <;> ring
    rw [h9] at *
    have h71 : 0 < (1 + 2 * a * b) * (1 + 2 * b * c) * (1 + 2 * c * a) := by positivity
    have h72 : ( (1 + 2 * b * c) * (1 + 2 * c * a) + (1 + 2 * a * b) * (1 + 2 * c * a) + (1 + 2 * a * b) * (1 + 2 * b * c) - (1 + 2 * a * b) * (1 + 2 * b * c) * (1 + 2 * c * a) ) ≥ 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, 
        mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
        mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith), 
        mul_pos (show 0 < c * a by nlinarith) (show 0 < a * b by nlinarith)
        ]
    apply div_nonneg
    linarith [h72]
    all_goals nlinarith
  linarith