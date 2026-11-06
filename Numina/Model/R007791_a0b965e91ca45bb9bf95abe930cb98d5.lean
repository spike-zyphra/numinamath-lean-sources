import Mathlib

theorem inequalities_281417 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 1 / c ≥ a + b + c) : 3 * a * b * c ≤ a + b + c := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : a * b + a * c + b * c ≥ a * b * c * (a + b + c) := by
    have h3 : a * b + a * c + b * c ≥ a * b * c * (a + b + c) := by
      have h4 : (1 / a + 1 / b + 1 / c - (a + b + c)) >= 0 := by linarith
      have pos1 : 0 < a * b * c := h1
      have h5 : (a * b + a * c + b * c) - (a * b * c * (a + b + c)) >= 0 := by
        have h7 : (1 / a + 1 / b + 1 / c - (a + b + c)) * (a * b * c) >= 0 := by
          apply mul_nonneg
          linarith
          all_goals positivity
        have h8 : (1 / a + 1 / b + 1 / c - (a + b + c)) * (a * b * c) = (a * b + a * c + b * c) - (a * b * c * (a + b + c)) := by
          field_simp
          <;> ring_nf <;> field_simp <;> ring
        linarith [h8, h7]
      linarith
    linarith
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]