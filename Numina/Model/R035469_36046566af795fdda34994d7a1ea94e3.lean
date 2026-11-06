import Mathlib

theorem inequalities_27570 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≥ 1 / a + 1 / b + 1 / c) :
    a ^ 3 + b ^ 3 + c ^ 3 ≥ a + b + c := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h2 : (a + b + c) * (a * b * c) ≥ a * b + a * c + b * c := by
    have h3 : 0 < a * b * c := h1
    have h4 : (a + b + c) * (a * b * c) ≥ ( (1 / a + 1 / b + 1 / c) ) * (a * b * c) := by
      apply mul_le_mul_of_nonneg_right
      linarith
      all_goals linarith
    have h5 : ( (1 / a + 1 / b + 1 / c) ) * (a * b * c) = a * b + a * c + b * c := by
      field_simp
      ring
    rw [h5] at h4
    nlinarith

  have h3 : a ^ 3 + b ^ 3 + c ^ 3 ≥ a + b + c := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - 1)), sq_nonneg (b * (b - 1)), sq_nonneg (c * (c - 1)), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
        mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
        mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)
    ]

  exact h3