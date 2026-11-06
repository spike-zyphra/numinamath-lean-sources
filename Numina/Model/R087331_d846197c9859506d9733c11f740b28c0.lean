import Mathlib

theorem inequalities_191165 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 1 / c ≥ a + b + c) :
    3 * a * b * c ≤ a + b + c := by
  have h1 : a * b + a * c + b * c ≥ a * b * c * (a + b + c) := by
    have h2 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
      field_simp
      ring
    have h3 : (1 / a + 1 / b + 1 / c) = (b * c + a * c + a * b) / (a * b * c) := by
      field_simp
      ring
    have h4 : a * b * c > 0 := mul_pos (mul_pos ha hb) hc
    have h5 : (1 / a + 1 / b + 1 / c) * (a * b * c) ≥ (a + b + c) * (a * b * c) := by
      have h6 : (1 / a + 1 / b + 1 / c) ≥ (a + b + c) := h
      have h8 : (1 / a + 1 / b + 1 / c) * (a * b * c) ≥ (a + b + c) * (a * b * c) := by
        apply mul_le_mul_of_nonneg_right
        linarith
        positivity
      linarith
    have h9 : (1 / a + 1 / b + 1 / c) * (a * b * c) = b * c + a * c + a * b := by
      calc
        (1 / a + 1 / b + 1 / c) * (a * b * c)
            = (b * c + a * c + a * b) / (a * b * c) * (a * b * c) := by rw [h3]
        _   = b * c + a * c + a * b := by
          field_simp
          <;> nlinarith
    nlinarith [h9, h5, h3, h2]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]