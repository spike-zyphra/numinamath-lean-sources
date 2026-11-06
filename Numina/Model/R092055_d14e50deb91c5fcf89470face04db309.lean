import Mathlib

theorem algebra_320517 {a b c : ℝ} (h₀ : a + b + c = 1) (h₁ : a^2 + b^2 + c^2 = 2) (h₂ : a^3 + b^3 + c^3 = 3) :
    a * b * c = 1 / 6 ∧ a^4 + b^4 + c^4 = 25 / 6 := by
  have h3 : a * b + b * c + c * a = -1 / 2 := by
    have sq : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by ring
    rw [h₀, h₁] at sq
    linarith
  have h4 : a * b * c = 1 / 6 := by
    have h5 : a^3 + b^3 + c^3 - 3 * (a * b * c) = (a + b + c) * ((a^2 + b^2 + c^2) - (a * b + b * c + c * a)) := by ring
    rw [h₀, h₁, h3] at h5
    linarith
  have h6 : a^4 + b^4 + c^4 = 25 / 6 := by
    have h7 : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 = -1 / 12 := by
      have h8 : (a * b + b * c + c * a)^2 = a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 2 * (a * b * c) * (a + b + c) := by ring
      rw [h3, h4, h₀] at h8
      linarith
    have sq2 : (a^2 + b^2 + c^2) ^ 2 = a^4 + b^4 + c^4 + 2 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) := by ring
    rw [h₁, h7] at sq2
    linarith
  exact ⟨h4, h6⟩