import Mathlib

def p (x : ℕ) := x ^ 2 + 3 * x + 2

theorem algebra_234529 : ∏ i ∈ Finset.Icc 1 2021, (1 - 2 / p i : ℚ) = 1012 / 3033 := by
  native_decide