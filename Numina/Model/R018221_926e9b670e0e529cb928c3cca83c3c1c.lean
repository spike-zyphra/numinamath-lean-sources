import Mathlib

def star (a b : ℤ) := a * a - b * b

theorem algebra_164537 : ∑ i ∈ Finset.range 18, star (i + 3) (i + 2) = 396 := by 
  have h2 : ∑ i in Finset.range 18, star (i + 3) (i + 2) = 396 := by
    native_decide
  exact h2