import Mathlib

theorem algebra_297708 {a b : ℝ} (ha : a ≠ 0) (h : ∀ x, ∃ y, y = a * x - 4 ∧ x = 8 * y - b) :
    a = 1 / 8 ∧ b = -32 := by
  have h1 := h 0
  rcases h1 with ⟨y1, hy1_eq, hx1_eq⟩
  have h_eq1 : y1 = -4 := by
    linarith
  have hb : b = -32 := by
    rw [h_eq1] at hx1_eq
    linarith 
  have h2 := h 1
  rcases h2 with ⟨y2, hy2_eq, hx2_eq⟩
  have eq1 : y2 = a - 4 := by
    linarith
  rw [hb] at hx2_eq
  have h_eq2 : y2 = -31 / 8 := by
    linarith
  have ha : a = 1 / 8 := by
    linarith [eq1, h_eq2]
  exact ⟨ha, hb⟩