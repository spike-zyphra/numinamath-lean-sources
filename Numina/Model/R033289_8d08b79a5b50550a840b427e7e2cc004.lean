import Mathlib

theorem algebra_120563 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a / (1 + a) + b / (1 + b) = 1) :
    a / (1 + b ^ 2) - b / (1 + a ^ 2) = a - b := by
  have h1 : a * (1 + b) + b * (1 + a) = (1 + a) * (1 + b) := by
    have ha1 : 1 + a ≠ 0 := by linarith
    have hb1 : 1 + b ≠ 0 := by linarith
    field_simp [ha1, hb1] at h ⊢
    linarith

  have h2 : a * b = 1 := by
    nlinarith [h1]

  have h3 : b = 1 / a := by
    have h4 : a * b = 1 := h2
    have ha1 : a ≠ 0 := by linarith
    field_simp [ha1]
    <;> nlinarith

  rw [h3]
  have ha1 : a ≠ 0 := by linarith
  field_simp [ha1]
  <;> nlinarith [sq_pos_of_pos ha]