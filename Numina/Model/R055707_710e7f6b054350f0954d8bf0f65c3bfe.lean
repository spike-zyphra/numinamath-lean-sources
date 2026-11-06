import Mathlib

theorem algebra_189815 (x y z : ℝ) (h₀ : x + y + z = 54) (h₁ : y = x + 10) (h₂ : z = 2 * y) :
    x = 6 ∧ y = 16 ∧ z = 32 := by 
  have hx : x = 6 := by 
    linarith [h₀, h₁, h₂]

  have hy : y = 16 := by 
    linarith [h₁, hx]

  have hz : z = 32 := by
    linarith [h₂, hy]

  exact ⟨hx, hy, hz⟩