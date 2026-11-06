import Mathlib

theorem algebra_215395 (x a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (x - a - b) / c + (x - b - c) / a + (x - c - a) / b = 3) :
    x = a + b + c := by
  have h1 : a * b * c ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · linarith
      · linarith
    · linarith
  have h2 : a * (x - a - b) * b + b * (x - b - c) * c + a * (x - c - a) * c = 3 * a * b * c := by
    have h3 : (x - a - b) / c + (x - b - c) / a + (x - c - a) / b = 3 := h
    have h4 : a * b * c ≠ 0 := h1
    field_simp [show c ≠ 0 by linarith [hc], show a ≠ 0 by linarith [ha], show b ≠ 0 by linarith [hb]] at h3 ⊢
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  nlinarith [h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]