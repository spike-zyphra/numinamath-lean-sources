import Mathlib

theorem algebra_326410 : (∏ i ∈ Finset.range 10, (4 * i + 3)^4 + 4) / (∏ i ∈ Finset.range 10, (4 * i + 5)^4 + 4) = 1 / 353 := by
  native_decide