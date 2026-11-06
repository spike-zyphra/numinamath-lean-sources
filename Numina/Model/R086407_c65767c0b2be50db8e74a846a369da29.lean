import Mathlib

theorem algebra_197156 {a b c d : ℝ} (h : ∀ x, 3 * x ^ 3 + 7 * x ^ 2 + 9 * x + 6 = a * (x + 1) ^ 3 + b * (x + 1) ^ 2 + c * (x + 1) + d) :
    a = 3 ∧ b = -2 ∧ c = 4 ∧ d = 1 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h (-1)
  have h1 : a + b + c + d = 6 := by
    linarith 
  have h2 : d = 1 := by
    linarith [eq4]
  have h3 : a + b + c = 5 := by
    linarith [h1, h2]
  have h_eq2 : 4 * a + 2 * b + c = 12 := by
    linarith [eq2, h2]
  have h_eq3 : 9 * a + 3 * b + c = 25 := by
    linarith [eq3, h2]
  have ha : a = 3 := by
    linarith [h_eq2, h_eq3, h3]
  have hb : b = -2 := by
    linarith [h_eq2, h_eq3, ha]
  have hc : c = 4 := by
    linarith [h3, ha, hb]
  exact ⟨ha, hb, hc, h2⟩