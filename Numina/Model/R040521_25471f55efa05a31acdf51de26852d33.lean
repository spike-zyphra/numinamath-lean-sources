import Mathlib

theorem algebra_147088 (a b : ℂ) (z₁ z₂ w₁ w₂ : ℂ)
    (h₁ : z₁ ≠ z₂) (h₂ : w₁ ≠ w₂)
    (h₃ : w₁ = a * z₁ + b) (h₄ : w₂ = a * z₂ + b) :
    a = (w₂ - w₁) / (z₂ - z₁) ∧ b = w₁ - a * z₁ := by
  have eq1 : a = (w₂ - w₁) / (z₂ - z₁) := by
    have h5 : z₂ - z₁ ≠ 0 := by
      intro h
      apply h₁
      have : z₁ = z₂ := by
        have h' : z₂ - z₁ = 0 := by
          simpa using h
        have : z₂ = z₁ := by
          calc
            z₂ = z₁ + (z₂ - z₁) := by ring
            _ = z₁ + 0 := by rw [h']
            _ = z₁ := by ring
        exact this.symm
      exact this
    have eq2 : w₂ - w₁ = a * (z₂ - z₁) := by
      calc
        w₂ - w₁ = (a * z₂ + b) - (a * z₁ + b) := by rw [h₄, h₃]
        _ = a * (z₂ - z₁) := by ring
    have h6 : z₂ - z₁ ≠ 0 := h5
    have h7 : a = (w₂ - w₁) / (z₂ - z₁) := by
      rw [eq2]
      field_simp [h6]
    exact h7
  have eq4 : b = w₁ - a * z₁ := by
    calc
      b = (a * z₁ + b) - a * z₁ := by ring
      _ = w₁ - a * z₁ := by rw [h₃]
  constructor
  · exact eq1
  · exact eq4