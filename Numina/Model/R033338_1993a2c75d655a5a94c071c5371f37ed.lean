import Mathlib

theorem algebra_9362 (a b : ℝ) (ha : a > 0) (hb : b > 0) (h : a = 3 * b) (hP : 3 ^ 2 / a ^ 2 + 0 ^ 2 / b ^ 2 = 1 ∨ 0^2 / a^2 + 3^2/b^2 = 1): (a = 3 ∧ b = 1) ∨ (a = 9 ∧ b = 3) := by
  rcases hP with (h1 | h2)
  · -- Assume 3^2 / a^2 + 0^2 / b^2 = 1
    have eq1 : 3 ^ 2 / a ^ 2 + 0 ^ 2 / b ^ 2 = 1 := h1
    have eq2 : 9 / a^2 = 1 := by
      norm_num at eq1 ⊢
      linarith
    have eq3 : a^2 = 9 := by
      field_simp at eq2 ⊢
      linarith
    have eq4 : a = 3 := by
      nlinarith [sq_pos_of_pos ha]
    have eq5 : b = 1 := by
      rw [eq4] at h
      linarith
    left
    exact ⟨eq4, eq5⟩
  · -- Assume 0^2 / a^2 + 3^2 / b^2 = 1
    have eq1 : 0^2 / a ^ 2 + 3 ^ 2 / b ^ 2 = 1 := h2
    have eq2 : 9 / b^2 = 1 := by
      norm_num at eq1 ⊢
      field_simp at eq1 ⊢
      linarith
    have eq3 : b^2 = 9 := by
      field_simp at eq2 ⊢
      linarith
    have eq4 : b = 3 := by
      nlinarith [sq_pos_of_pos hb]
    have eq5 : a = 9 := by
      rw [eq4] at h
      linarith
    right
    exact ⟨eq5, eq4⟩