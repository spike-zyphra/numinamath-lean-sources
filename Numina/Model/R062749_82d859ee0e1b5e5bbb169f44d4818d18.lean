import Mathlib

theorem algebra_236798 {a b c : ℕ} (h₀ : a * b * c = 240) (h₁ : a * b = 60) (h₂ : a * c = 24) :
    a = 6 ∧ b = 10 ∧ c = 4 := by
  have h3 : c = 4 := by
    have eq1 : a * b = 60 := h₁
    have eq2 : a * b * c = 240 := h₀
    have h4 : a * b * c = (a * b) * c := by ring
    rw [h4] at eq2
    rw [eq1] at eq2
    have : 60 * c = 240 := eq2
    -- solving equation 60 * c = 240
    omega
  have h4 : a = 6 := by
    rw [show c = 4 by exact h3] at h₂
    -- solving equation a * 4 = 24
    omega
  have h5 : b = 10 := by
    rw [show a = 6 by exact h4] at h₁
    -- solving equation 6 * b = 60
    omega
  exact ⟨h4, h5, h3⟩