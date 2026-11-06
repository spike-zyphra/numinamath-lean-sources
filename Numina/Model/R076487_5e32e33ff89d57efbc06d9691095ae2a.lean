import Mathlib

theorem algebra_160978 (a b c d : ℤ) (h₀ : a ≠ c) :
    (a - c) ∣ (a * b + c * d) ↔ (a - c) ∣ (a * d + b * c) := by
  constructor
  · -- Assume (a - c) divides (a * b + c * d), prove (a - c) divides (a * d + b * c)
    intro h
    have h₁ : a * b + c * d - (a * d + b * c) = (b - d) * (a - c) := by
      ring
    have h₂ : (a - c) ∣ (a * b + c * d) := h
    have h₃ : (a - c) ∣ (b - d) * (a - c) := by
      use (b - d)
      ring
    have h₄ : (a - c) ∣ ((a * b + c * d) - ((b - d) * (a - c))) := by
      apply Int.dvd_sub h₂ h₃
    have h₅ : (a * d + b * c) = (a * b + c * d) - ((b - d) * (a - c)) := by
      linarith [h₁]
    rw [h₅] at *
    exact h₄
  · -- Assume (a - c) divides (a * d + b * c), prove (a - c) divides (a * b + c * d)
    intro h
    have h₁ : a * b + c * d - (a * d + b * c) = (b - d) * (a - c) := by
      ring
    have h₂ : (a - c) ∣ (a * d + b * c) := h
    have h₃ : (a - c) ∣ (b - d) * (a - c) := by
      use (b - d)
      ring
    have h₄ : (a - c) ∣ ((a * d + b * c) + (b - d) * (a - c)) := by
      apply dvd_add h₂ h₃
    have h₅ : a * b + c * d = (a * d + b * c) + (b - d) * (a - c) := by
      linarith [h₁]
    rw [h₅] at *
    exact h₄