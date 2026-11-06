import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_146717 (a : ℝ) :
  (∀ x : ℝ, x^2 + (a + 4) * x + 9 > 0) ↔ -10 < a ∧ a < 2 := by
    constructor
    · -- Forward direction: if the quadratic expression is positive definite, then $-10 < a < 2$
      intro h
      have h1 : ∀ x : ℝ, x^2 + (a + 4) * x + 9 > 0 := h
      have h2 : ((-(a + 4) / 2) ^ 2 + (a + 4) * (-(a + 4) / 2) + 9 > 0) := h1 (-(a + 4) / 2)
      have h3 : 9 - (a + 4) ^ 2 / 4 > 0 := by
        nlinarith
      have h4 : (a + 4) ^ 2 < 36 := by nlinarith
      constructor
      · -- Solving (a + 4)^2 < 36 gives -6 < a + 4, hence -10 < a
        nlinarith
      · -- Solving (a + 4)^2 < 36 gives a + 4 < 6, hence a < 2
        nlinarith
    · -- Backward direction: if $-10 < a < 2$, then the quadratic expression is positive definite
      rintro ⟨h1, h2⟩
      intro x
      -- Completing the square
      have h3 : (a + 4) ^ 2 < 36 := by nlinarith 
      -- Using the fact that x^2 + (a+4)x + 9 can be written as (x + (a+4)/2)^2 - (a+4)^2/4 + 9
      nlinarith [sq_nonneg (x + (a + 4) / 2)]