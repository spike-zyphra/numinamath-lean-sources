import Mathlib

theorem algebra_105717 (grandfather son1 son2 : ℕ)
    (h₀ : grandfather = 3 * son1) (h₁ : grandfather = 4 * son2)
    (h₂ : son1 + son2 = 49) :
    grandfather = 84 := by
  have h3 : 3 * son1 = 4 * son2 := by 
    linarith
  have h4 : son2 = 21 := by
    omega 
  have h5 : son1 = 28 := by
    omega
  have h6 : grandfather = 84 := by 
    linarith [h₀, h5]
  exact h6