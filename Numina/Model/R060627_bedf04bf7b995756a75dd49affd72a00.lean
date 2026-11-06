import Mathlib

theorem algebra_21834 {x y z w : ℕ} (h₀ : x + y + z + w = 20)
    (h₁ : x = y - 3) (h₂ : y = z + 2) (h₃ : w = 2 * y) :
    w = 10 := by 
  omega