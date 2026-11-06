import Mathlib

/- What is the sum of all the three-digit positive integers? -/
theorem algebra_10711 : ∑ n in Finset.Icc 100 999, n = 494550 := by
  native_decide
