import Mathlib

theorem algebra_263176 (a b : ℝ) (h : ∀ x, a * (x + b) = 3 * x + 12) : a + b = 7 := by
  have eq1 := h 0
  have eq2 := h 1
  have h1 : a * b = 12 := by
    linarith
  have h2 : a * (1 + b) = 15 := by
    linarith
  have eq3 : a + (a * b) = 15 := by
    linarith [h2]
  have ha : a = 3 := by
    linarith [eq3, h1]
  have hb : b = 4 := by
    rw [ha] at h1 
    linarith
  linarith [ha, hb]