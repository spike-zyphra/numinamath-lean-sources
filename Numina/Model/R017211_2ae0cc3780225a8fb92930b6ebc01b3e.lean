import Mathlib

theorem algebra_20280 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b^2 = 5) :
    a^4 + b^8 ≥ 50 := by
  -- From the condition, we get a = 5 / (b^2)
  have h0 : a = 5 / (b^2) := by
    have hb2_pos : b^2 > 0 := by nlinarith
    field_simp
    nlinarith

  have h11 : a^4 + b^8 = (5 / (b^2)) ^ 4 + b^8 := by
    rw [show a^4 = (5 / (b^2)) ^ 4 by rw [show a = 5 / (b^2) by linarith [h0]]]
  have h14 : (5 / (b^2)) ^ 4 = 625 / (b^8) := by
    field_simp
    <;> nlinarith

  have h17 : a^4 + b^8 = 625 / (b^8) + b^8 := by
    rw [h11]
    rw [h14]

  have h6_pos : b^8 > 0 := by positivity

  have h7 : 625 / (b^8) + b^8 - 50 ≥ 0 := by
    have h8 : b^8 > 0 := h6_pos
    have h9 : 625 / (b^8) + b^8 - 50 = (625 + (b^8)^2 - 50 * (b^8)) / (b^8) := by
      field_simp
      ring
    rw [h9]

    apply div_nonneg
    · -- Show that 625 + (b^8)^2 - 50 * (b^8) ≥ 0
      have h5 : (b^8 - 25: ℝ) ^ 2 ≥ 0 := by nlinarith
      nlinarith [sq_nonneg (b^8 - 25)]
    · -- Show that b^8 > 0
      linarith

  linarith [h17, h7]