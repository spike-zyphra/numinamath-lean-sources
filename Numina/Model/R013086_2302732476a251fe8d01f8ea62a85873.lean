import Mathlib

theorem algebra_292672 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a * b * (a + b) = 1) :
    a / (a^3 + a + 1) = b / (b^3 + b + 1) := by

  have h1 : a * (b ^ 3 + b + 1) = b * (a ^ 3 + a + 1) := by
    have h2 : a * b * (a + b) = 1 := h
    have h3 : a * (b ^ 3 + b + 1) - b * (a ^ 3 + a + 1) = 0 := by
      have h4 : a * (b ^ 3 + b + 1) - b * (a ^ 3 + a + 1) = a * b * (b ^ 2 - a ^ 2) + (a - b) := by
        ring
      rw [h4]
      have h5 : a * b * (b ^ 2 - a ^ 2) = (b - a) := by
        have h7 : a * b * (a + b) = 1 := h
        have h8 : a * b * (b ^ 2 - a ^ 2) = (a * b * (a + b)) * (b - a) := by
          ring_nf
        rw [h8, h7]
        <;> nlinarith
      nlinarith [h5]
    linarith

  have h2 : a / (a^3 + a + 1) = b / (b^3 + b + 1) := by
    field_simp [(show a^3 + a + 1 ≠ 0 by positivity), (show b^3 + b + 1 ≠ 0 by positivity)] at *
    linarith [h1]
  exact h2