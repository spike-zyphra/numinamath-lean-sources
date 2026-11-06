import Mathlib

theorem algebra_2329 (α ω : ℝ) (hα : α ≠ 0) (hω : ω ≠ 0)
    (h₁ : α * ω = 60) (h₂ : (α - 1) * (ω - 1) = 40) :
    (α - 2) * (ω - 2) = 22 := by
  have h3 : α + ω = 21 := by
    nlinarith [h₁, h₂]

  nlinarith [h₁, h3]