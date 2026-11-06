import Mathlib

theorem algebra_277096 {x y z w : ℕ}
    (h₀ : x * 1 = y * 3) (h₁ : y * 2 = z * 3) (h₂ : z * 5 = w * 7)
    (h₃ : w = 24) :
    x + y + z + w = 160 := by 
  subst h₃
  omega