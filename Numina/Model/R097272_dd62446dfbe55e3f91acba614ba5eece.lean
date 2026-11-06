import Mathlib

theorem algebra_235441 (v u m t : ℝ) (h₀ : v > 0) (h₁ : u > 0) (h₂ : m > 0)
    (h₃ : t > 0) (h₄ : v = 2 * u) (h₅ : u = 5 * t) (h₆ : v * 100 = u * 100 - m * 100 - t * 100) :
    m * 100 - t * 100 = 40 := by
  nlinarith [h₄, h₅, h₆, h₀, h₁, h₂, h₃]