import Mathlib

theorem inequalities_601183 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 ≤ 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1)) :
    a * b + a * c + b * c ≤ a + b + c := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : 0 < a + b + 1 := by
    linarith
  have h3 : 0 < b + c + 1 := by
    linarith
  have h4 : 0 < c + a + 1 := by
    linarith
  have h5 : (a + b + 1) * (b + c + 1) * (c + a + 1) ≤ (b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) := by
    have h6 : 0 < (a + b + 1) * (b + c + 1) * (c + a + 1) := by positivity
    have h7 : (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1) ≥ 0 := by
      linarith [h]
    have h8 : (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1) =
          ((b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (c + a + 1)) / ((a + b + 1) * (b + c + 1) * (c + a + 1)) := by
      field_simp
      <;> ring
    rw [h8] at h7
    apply (div_nonneg_iff).mp at h7
    cases h7 with
    | inl h1 =>
      nlinarith
    | inr h2 =>
      nlinarith [show (a + b + 1) * (b + c + 1) * (c + a + 1) > 0 by positivity]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]