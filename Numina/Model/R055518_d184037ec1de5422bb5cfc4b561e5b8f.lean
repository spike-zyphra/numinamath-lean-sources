import Mathlib

theorem algebra_115280 (x y : ℕ) (h₀ : x + y = 300) (h₁ : 12 * x + 6 * y = 2400) :
    x = 100 ∧ y = 200 := by 
  have hx : x = 100 := by
    omega 
  have hy : y = 200 := by
    omega 
  exact ⟨hx, hy⟩