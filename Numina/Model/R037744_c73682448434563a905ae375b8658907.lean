import Mathlib

theorem algebra_288235 {w : ℝ} (hw : w ≠ 0) (h : ∃ d, 1 / w + d = 1 / 2 ∧ 1 / 2 + d = 1 / 3 ∧ 1 / 3 + d = 1 / 6) :
    w = 3 / 2 := by
  rcases h with ⟨d, h1, h2, h3⟩
  have h4 : d = -1 / 6 := by
    linarith
  have h6 : 1 / w = 2 / 3 := by 
    rw [h4] at h1
    linarith
  have hw_eq : w = 3 / 2 := by 
    field_simp at h6 ⊢
    linarith
  exact hw_eq