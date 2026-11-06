import Mathlib

theorem negated_algebra_45877 (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a * (1 - b)
    = 1 / 4 ∧ b * (1 - c)
    = 1 / 4 ∧ c * (1 - a)
    = 1 / 4) :
    a = b ∧ b = c := by
  rcases h with ⟨h1, h2, h3⟩
  have eq1 : a - a * b = 1 / 4 := by linarith
  have eq2 : b - b * c = 1 / 4 := by linarith
  have eq3 : c - c * a = 1 / 4 := by linarith
  have h4 : a = b := by
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      h1, h2, h3, 
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < b * c from mul_pos hb hc), 
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < c * a from mul_pos hc ha), 
      mul_pos (show 0 < b * c from mul_pos hb hc) (show 0 < c * a from mul_pos hc ha)
    ]
  have h5 : b = c := by 
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      h1, h2, h3, 
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < b * c from mul_pos hb hc), 
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < c * a from mul_pos hc ha), 
      mul_pos (show 0 < b * c from mul_pos hb hc) (show 0 < c * a from mul_pos hc ha)
    ]
  exact ⟨h4, h5⟩