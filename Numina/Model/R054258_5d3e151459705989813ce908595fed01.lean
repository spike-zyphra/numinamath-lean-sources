import Mathlib

def triangle (a b : ℤ) := a * a - 2 * b

theorem algebra_293866 : ∑ i ∈ Finset.range 99, triangle (i + 1) (i + 2) = 318252 := by 
  native_decide