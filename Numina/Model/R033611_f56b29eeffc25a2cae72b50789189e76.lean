import Mathlib

theorem inequalities_602887 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 ≤ 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1)) :
    a * b + b * c + c * a ≤ a + b + c := by
  have h1 : 0 < a + b + 1 := by linarith
  have h2 : 0 < b + c + 1 := by linarith
  have h3 : 0 < c + a + 1 := by linarith
  have h4 : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1 ≥ 0 := by linarith
  have h5 : (b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (c + a + 1) ≥ 0 := by
    have h6 : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1 =
      ((b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (c + a + 1)) / ((a + b + 1) * (b + c + 1) * (c + a + 1)) := by
      field_simp
      ring
    rw [h6] at h4
    have h7 : (a + b + 1) * (b + c + 1) * (c + a + 1) > 0 := by positivity
    have h8 : ((b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (c + a + 1)) / ((a + b + 1) * (b + c + 1) * (c + a + 1)) ≥ 0 := by linarith
    have h9 : (b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (c + a + 1) ≥ 0 := by
      apply div_nonneg_iff.mp at h8
      cases h8 with
      | inl h1 =>
        nlinarith
      | inr h2 =>
        nlinarith
    linarith
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
    sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc 
  ]