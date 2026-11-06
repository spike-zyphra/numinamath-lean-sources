import Mathlib

theorem algebra_99564 {a b c : ℤ} (h₀ : a * b + c = 94) (h₁ : a + b * c = 95) :
    b = 0 ∨ b = 2 ∨ b = 31 ∨ b = 32 := by
  have h2 : (1 - b) * (a - c) = 1 := by
    nlinarith
  have h3 : (1 - b) = 1 ∨ (1 - b) = -1 := by
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact h2
  rcases h3 with (h3 | h3)
  · -- Case $1 - b = 1$, so $b = 0$.
    have h4 : b = 0 := by 
      linarith 
    left 
    exact h4 
  · -- Case $1 - b = -1$, so $b = 2$.
    have h4 : b = 2 := by 
      linarith 
    right 
    left 
    exact h4