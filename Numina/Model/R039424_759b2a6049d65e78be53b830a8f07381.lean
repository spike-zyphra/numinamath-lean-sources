import Mathlib

theorem algebra_22017 {A B : ℝ} (h : ∀ x : ℝ, x ≠ 1 ∧ x ≠ -1 → A / (x - 1) + B / (x + 1) = (x + 2) / (x ^ 2 - 1)) :
    A - B = 2 := by

  have eq1 := h 0 ⟨by norm_num, by norm_num⟩
  have eq2 := h 2 ⟨by norm_num, by norm_num⟩

  field_simp at eq1 eq2

  linarith