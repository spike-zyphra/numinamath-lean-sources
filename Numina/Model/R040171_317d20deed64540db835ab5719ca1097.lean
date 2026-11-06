import Mathlib

theorem inequalities_91001 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≥ 1 / a + 1 / b + 1 / c) :
    a / b + b / c + c / a ≥ 1 / (a * b) + 1 / (b * c) + 1 / (c * a) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : a / b + b / c + c / a - (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) ≥ 0 := by
    have eq5 : a / b + b / c + c / a - (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) = (a^2 * c + b^2 * a + c^2 * b - (a + b + c)) / (a * b * c) := by
      field_simp
      ring
    have h7 : a^2 * c + b^2 * a + c^2 * b ≥ a + b + c := by
      have h2' : a + b + c ≥ 1 / a + 1 / b + 1 / c := by linarith
      have h8 : (a + b + c) * (a * b * c) ≥ a * b + a * c + b * c := by
        have h2'' : a + b + c ≥ 1 / a + 1 / b + 1 / c := h2'
        have h9 : (a + b + c) - (1 / a + 1 / b + 1 / c) ≥ 0 := by linarith
        have eq1 : (a + b + c) - (1 / a + 1 / b + 1 / c) = ((a + b + c) * (a * b * c) - (a * b + a * c + b * c)) / (a * b * c) := by
          field_simp
          <;> ring
        rw [eq1] at h9
        have hx1 : (a + b + c) * (a * b * c) - (a * b + a * c + b * c) ≥ 0 := by
          have hx2 : a * b * c > 0 := h1
          apply (div_nonneg_iff).mp at h9
          cases h9 with
          | inl h9 =>
            linarith
          | inr h9 =>
            linarith
        linarith
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h8
      ]
    have hx3 : (a^2 * c + b^2 * a + c^2 * b - (a + b + c)) ≥ 0 := by
      linarith
    rw [eq5]
    apply div_nonneg
    linarith
    all_goals nlinarith [h1]

  linarith