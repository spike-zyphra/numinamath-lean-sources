import Mathlib

theorem algebra_285278 (J Y : ℕ) (h₀ : J + Y = 70) (h₀ : ∃ x, x ≤ J ∧ x ≤ Y ∧ J - x = Y ∧ Y - x = ((J - x) / 2 : ℚ)) :
    J = 42 := by
  obtain ⟨x, h₀, h₁, h₂, h₃⟩ := h₀
  field_simp at h₃
  norm_cast at h₃
  omega