import Mathlib

theorem algebra_323672 : (∑ i ∈ Finset.range 1996, (-1 : ℤ)^i * (i + 1)^3) % 10 = 0 := by
  native_decide