import Mathlib

def S (n : ℕ) := ∑ i in Finset.range n, (-1 : ℤ)^i * (i + 1)

theorem algebra_203102 : S 17 + S 33 + S 50 = 1 := by 
  native_decide