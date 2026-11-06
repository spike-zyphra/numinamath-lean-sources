import Mathlib

theorem algebra_114569 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a / (1 + b) + b / (1 + a) = 1) : a^3 + b^3 = a + b := by
  have h1 : 0 < (1 + a) * (1 + b) := by
    apply mul_pos
    linarith
    linarith
  have h2 : a * (1 + a) + b * (1 + b) = (1 + b) * (1 + a) := by
    have denom_pos1 : 1 + b > 0 := by linarith
    have denom_pos2 : 1 + a > 0 := by linarith
    field_simp at h ⊢
    nlinarith [h, mul_pos ha hb, mul_pos ha (show 0 < 1 by linarith), mul_pos hb (show 0 < 1 by linarith)]
  have h3 : a^2 + b^2 = 1 + a * b := by
    nlinarith
  have h4 : a^3 + b^3 = (a + b) * (a^2 + b^2 - a * b) := by
    ring
  rw [h4]
  rw [h3]
  all_goals 
    ring_nf <;> nlinarith