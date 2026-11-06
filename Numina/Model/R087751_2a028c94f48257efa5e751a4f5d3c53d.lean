import Mathlib

theorem inequalities_599473 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 + b * c) / (b + c) + (b^2 + c * a) / (c + a) + (c^2 + a * b) / (a + b) ≥
    a + b + c := by
  have pos1 : 0 < b + c := by nlinarith
  have pos2 : 0 < c + a := by nlinarith
  have pos3 : 0 < a + b := by nlinarith
  have h2 : (a^2 + b * c) / (b + c) + (b^2 + c * a) / (c + a) + (c^2 + a * b) / (a + b) - (a + b + c) ≥ 0 := by
    have h3 : (a^2 + b * c) / (b + c) + (b^2 + c * a) / (c + a) + (c^2 + a * b) / (a + b) - (a + b + c) =
      ((a^2 + b * c) / (b + c) - a) + ((b^2 + c * a) / (c + a) - b) + ((c^2 + a * b) / (a + b) - c) := by
      ring_nf
      <;> field_simp
      <;> ring
    rw [h3]
    have h4 : ((a^2 + b * c) / (b + c) - a) = (a - b) * (a - c) / (b + c) := by
      field_simp
      ring
    have h5 : ((b^2 + c * a) / (c + a) - b) = (b - c) * (b - a) / (c + a) := by
      field_simp
      ring
    have h6 : ((c^2 + a * b) / (a + b) - c) = (c - a) * (c - b) / (a + b) := by
      field_simp
      ring
    rw [h4, h5, h6]
    have h7 : (a - b) * (a - c) / (b + c) + (b - c) * (b - a) / (c + a) + (c - a) * (c - b) / (a + b) ≥ 0 := by
      have h8 : (a - b) * (a - c) / (b + c) + (b - c) * (b - a) / (c + a) + (c - a) * (c - b) / (a + b) =
        ((a - b) * (a - c) * (c + a) * (a + b) + (b - c) * (b - a) * (b + c) * (a + b) + (c - a) * (c - b) * (b + c) * (c + a))
        / ((b + c) * (c + a) * (a + b)) := by
        field_simp
        <;> ring
      rw [h8]
      have h9 : (a - b) * (a - c) * (c + a) * (a + b) + (b - c) * (b - a) * (b + c) * (a + b) + (c - a) * (c - b) * (b + c) * (c + a) ≥ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
                 ]
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith