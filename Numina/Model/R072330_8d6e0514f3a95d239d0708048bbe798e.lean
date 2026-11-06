import Mathlib

def u : ℕ → ℕ
| n => n % 10

def a : ℕ → ℤ
| n => u (7 * n) - u n

theorem number_theory_188637 : ∑ i in Finset.Icc 1 2020, a i = 0 := by
  native_decide