import Mathlib

theorem algebra_228788 : ∑ i ∈ Finset.range 2019, (-1 : ℤ)^i * (i + 1) * (i + 2) * ((i + 1) + (i + 2)) = 8242405980 := by 
  native_decide