import Mathlib

theorem algebra_199195 (a b c : ℤ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c)
    (h₂ : a ≠ b) (h₃ : b ≠ c) (h₄ : a ≠ c) :
    (a + b + c) ∣ (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) ↔
    (a + b + c) ∣ (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) := by
  constructor
  · -- Assume (a + b + c) divides (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)
    intro h
    have h2 : (a + b + c) ∣ (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) := by
      obtain ⟨k, hk⟩ := h
      use (k - (a ^ 2 * (b - c) + b ^ 2 * (c - a) + c ^ 2 * (a - b)))
      linarith [hk]
    exact h2
  · -- Assume (a + b + c) divides (a * b ^ 3 + b * c ^ 3 + c * a ^ 3)
    intro h
    have h2 : (a + b + c) ∣ (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) := by
      obtain ⟨k, hk⟩ := h
      use (k + (a ^ 2 * (b - c) + b ^ 2 * (c - a) + c ^ 2 * (a - b)))
      linarith [hk]
    exact h2