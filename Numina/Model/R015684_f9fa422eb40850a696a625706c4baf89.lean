import Mathlib

theorem inequalities_181483 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c > 1 / a + 1 / b + 1 / c) :
    3 / a / b / c ≤ a + b + c := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h3 : a * b * c * (a + b + c) > a * b + a * c + b * c := by
    have h4 : a + b + c - (1 / a + 1 / b + 1 / c) > 0 := by linarith
    have h6 : (a + b + c) - (1 / a + 1 / b + 1 / c) = (a * b * c * (a + b + c) - (a * b + a * c + b * c)) / (a * b * c) := by
      field_simp
      ring
    rw [h6] at h4
    have h7 : a * b * c > 0 := h1
    have h8 : (a * b * c * (a + b + c) - (a * b + a * c + b * c)) / (a * b * c) > 0 := h4
    apply div_pos_iff.mp at h8
    cases h8 with
    | inl h9 =>
      linarith
    | inr h9 =>
      nlinarith
  suffices 3 ≤ a * b * c * (a + b + c) by
    have h5 : 3 / a / b / c = 3 / (a * b * c) := by
      field_simp
      <;> ring
    rw [h5]
    have h6 : a * b * c > 0 := h1
    have h13 : (a * b * c) * (a + b + c) ≥ 3 := by
      nlinarith
    have h7 : (3 / (a * b * c) : ℝ) ≤ a + b + c := by
      have h8 : (a * b * c) * (a + b + c) ≥ 3 := h13
      have h9 : 0 < a * b * c := h1
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    exact h7
  · -- Show $3 \leq a * b * c * (a + b + c)$.
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
      mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
      mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)]