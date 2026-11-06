import Mathlib

open Complex

theorem algebra_5473  :
  ∀ (ω : ℂ)
  (hω₁ : ω^3 = 1)
  (hω₂ : 1 + ω + ω^2 = 0), ∀ (x y : ℂ), x^2 + x * y + y^2 = 0 ↔ (x - ω * y) * (x - ω ^ 2 * y) = 0  := by
  intro ω hω₁ hω₂ x y
  constructor
  · -- Assume x^2 + x * y + y^2 = 0, prove (x - ω * y) * (x - ω ^ 2 * y) = 0
    intro h
    have h1 : ω + ω^2 = -1 := by
      calc
        ω + ω^2 = (1 + ω + ω^2) - 1 := by ring
        _ = 0 - 1 := by rw [hω₂]
        _ = -1 := by ring
    calc
      (x - ω * y) * (x - ω ^ 2 * y) = x^2 - (ω + ω^2) * (x * y) + ω^3 * y^2 := by ring_nf
      _ = x^2 - (-1) * (x * y) + 1 * y^2 := by rw [h1, hω₁]
      _ = x^2 + x * y + y^2 := by ring_nf
      _ = (0 : ℂ) := by rw [h]
  · -- Assume (x - ω * y) * (x - ω ^ 2 * y) = 0, prove x^2 + x * y + y^2 = 0
    intro h
    have h1 : ω + ω^2 = -1 := by
      calc
        ω + ω^2 = (1 + ω + ω^2) - 1 := by ring
        _ = 0 - 1 := by rw [hω₂]
        _ = -1 := by ring
    have h2 : (x - ω * y) * (x - ω ^ 2 * y) = x^2 + x * y + y^2 := by
      calc
        (x - ω * y) * (x - ω ^ 2 * y) = x^2 - (ω + ω^2) * (x * y) + ω^3 * y^2 := by ring_nf
        _ = x^2 - (-1) * (x * y) + 1 * y^2 := by rw [h1, hω₁]
        _ = x^2 + x * y + y^2 := by ring_nf
    rw [h2] at h
    assumption