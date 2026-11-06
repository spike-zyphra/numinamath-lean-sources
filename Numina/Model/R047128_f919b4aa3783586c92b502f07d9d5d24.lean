import Mathlib

theorem inequalities_90501 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 ≤ 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1)) :
    a + b + c ≥ a * b + b * c + c * a := by
  have h1 : 0 < a + b + 1 := by
    linarith
  have h2 : 0 < b + c + 1 := by
    linarith
  have h3 : 0 < c + a + 1 := by
    linarith
  have h5 : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1 ≥ 0 := by linarith
  have h6 : (b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) ≥ (a + b + 1) * (b + c + 1) * (c + a + 1) := by
    have h7 : 0 < (a + b + 1) * (b + c + 1) * (c + a + 1) := by positivity
    have h8 : 1 - (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1)) ≤ 0 := by
      linarith
    have h9 : 1 - (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1)) =
        ( (a + b + 1) * (b + c + 1) * (c + a + 1) - 
            ( (b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) ) ) / ( (a + b + 1) * (b + c + 1) * (c + a + 1) ) := by 
      field_simp
      <;> ring
    rw [h9] at h8
    apply (div_nonpos_iff).mp at h8
    cases h8 with
    | inl h10 =>
      nlinarith
    | inr h11 =>
      nlinarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
  ]