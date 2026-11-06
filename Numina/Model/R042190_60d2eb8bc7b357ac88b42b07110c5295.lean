import Mathlib

theorem algebra_18686 (x dragonfruit starfruit rambutan: ℝ) (h₀ : 0 < x) (h₁ : dragonfruit = x - 4) (h₂ : starfruit = rambutan - 5) (h₃ : rambutan = dragonfruit + 2 * x) :
  1 * rambutan + 2 * starfruit + 3 * dragonfruit = 12 * x - 34 := by
  have h₄ : rambutan = 3 * x - 4 := by
    rw [h₃, h₁]
    linarith 
  have h₅ : starfruit = 3 * x - 9 := by
    rw [h₂, h₄]
    linarith
  rw [h₅, h₄, h₁]
  ring