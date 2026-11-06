import Mathlib

theorem algebra_197220 (father son daughter : ℕ)
    (h₀ : father - 10 = son + daughter)
    (h₁ : father - (10 + 8 * son) = daughter - (10 + 3 * son))
    (h₂ : daughter - father > 20)
    (h₃ : son - father < 40) :
    father = 70 ∧ son = 45 ∧ daughter = 35 := by 
  omega