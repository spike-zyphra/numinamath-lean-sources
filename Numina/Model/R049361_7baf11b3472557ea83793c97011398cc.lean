import Mathlib

theorem algebra_216707 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : 1 / a + 1 / b = 1 / 15) (h₂ : 1 / a + 1 / c = 1 / 8)
    (h₃ : 1 / a + 1 / b + 1 / c = 1 / 6) :
    a = 40 ∧ b = 24 ∧ c = 10 := by
  have ha : a > 0 := by linarith [h₀.left, h₀.right.left, h₀.right.right]
  have hb : b > 0 := by linarith [h₀.left, h₀.right.left, h₀.right.right]
  have hc : c > 0 := by linarith [h₀.left, h₀.right.left, h₀.right.right]
  have eq1 : a * b = 15 * (a + b) := by
    field_simp at h₁
    nlinarith
  have eq2 : a * c = 8 * (a + c) := by
    field_simp at h₂
    nlinarith
  have eq3 : a * b * c = 6 * (a * b + a * c + b * c) := by
    field_simp at h₃
    nlinarith
  have h4 : a = 40 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
              eq1, eq2, eq3]
  have h5 : b = 24 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
              eq1, eq2, eq3]
  have h6 : c = 10 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
              eq1, eq2, eq3]
  exact ⟨h4, h5, h6⟩