import Mathlib

theorem inequalities_68274 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h₀ : a + b + c = 0) (h₁ : a * b * c < 0) :
    (a ^ 2 + b ^ 2) / c + (b ^ 2 + c ^ 2) / a + (c ^ 2 + a ^ 2) / b > 0 := by
  have pos2 : (a ^ 2 + b ^ 2) / c + (b ^ 2 + c ^ 2) / a + (c ^ 2 + a ^ 2) / b = ((a ^ 2 + b ^ 2) * (a * b) + (b ^ 2 + c ^ 2) * (b * c) + (c ^ 2 + a ^ 2) * (a * c)) / (a * b * c) := by
    field_simp [hc, ha, hb]
    <;> ring
  rw [pos2]
  have h5 : ((a ^ 2 + b ^ 2) * (a * b) + (b ^ 2 + c ^ 2) * (b * c) + (c ^ 2 + a ^ 2) * (a * c)) < 0 := by
    have h6 : c = -a - b := by
      linarith
    rw [h6]
    nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero (show (-a - b) ≠ 0 by 
      intro h 
      apply hc 
      linarith
    ), sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a * (a + b)), sq_nonneg (b * (a + b)), sq_nonneg (a * b), sq_pos_of_ne_zero (show a * b ≠ 0 by
      apply mul_ne_zero 
      exact ha
      exact hb
    ), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb
    ]
  have h8 : (a * b * c) < 0 := h₁
  apply div_pos_of_neg_of_neg
  · linarith [h5]
  · linarith [h8]