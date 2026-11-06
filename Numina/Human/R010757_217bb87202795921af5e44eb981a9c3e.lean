import Mathlib

/- Alice’s age in years is twice Eve’s age in years. In $10$ years, Eve will be as old as Alice is now. Compute Alice’s age in years now. -/
theorem algebra_64986 (a e : ℕ) (h₀ : a = 2 * e) (h₁ : e + 10 = a) :
    a = 20 := by
  linarith