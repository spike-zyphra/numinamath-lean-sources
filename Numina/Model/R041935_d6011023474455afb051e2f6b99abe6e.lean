import Mathlib

theorem inequalities_322673 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 2 / b + 3 / c = 1) :
    a + 2 * b + 3 * c ≥ 36 := by
  have h1 : b * c + 2 * a * c + 3 * a * b = a * b * c := by
    have h2 : 0 < a * b * c := by positivity
    have h3 : 1 / a + 2 / b + 3 / c = 1 := h
    field_simp at h3
    nlinarith
  nlinarith [sq_nonneg (a - 6), sq_nonneg (b - 6), sq_nonneg (c - 6), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]