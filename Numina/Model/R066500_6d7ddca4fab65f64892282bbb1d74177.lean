import Mathlib

theorem algebra_322342 {a b : ℝ} (ha : 0 < b) (hb : b < a)
    (h : a^2 + b^2 = 6 * a * b) : (a + b) / (a - b) = Real.sqrt 2 := by
  have hab : 0 < a - b := by linarith
  have h1 : ((a + b) / (a - b)) ^ 2 = 2 := by
    have h2 : a - b ≠ 0 := by linarith
    field_simp
    nlinarith
  have h2 : (a + b) / (a - b) > 0 := by
    apply div_pos
    all_goals linarith
  have h3 : (a + b) / (a - b) = Real.sqrt 2 := by
    have h4 : ((a + b) / (a - b)) ^ 2 = (2 : ℝ) := h1
    have h5 : 0 ≤ (a + b) / (a - b) := by linarith
    have h6 : Real.sqrt (((a + b) / (a - b)) ^ 2) = Real.sqrt (2 : ℝ) := by
      rw [h4]
    have h7 : Real.sqrt (((a + b) / (a - b)) ^ 2) = (a + b) / (a - b) := by
      rw [Real.sqrt_sq]
      linarith
    linarith
  exact h3