import Mathlib

theorem number_theory_312535 (a b c : ℕ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c)
    (h₃ : 13 + a = 9 + b) (h₄ : 9 + b = 3 + c) :
    a^2 + b^2 + c^2 - a * b - b * c - c * a = 76 := by
  have h₅ : b = a + 4 := by
    omega
  have h₆ : c = a + 10 := by
    rw [h₅] at h₄
    omega
  rw [h₅, h₆]
  <;> ring_nf <;> omega