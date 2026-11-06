import Mathlib

open BigOperators Finset Real

theorem algebra_2959 : (∑ i ∈ range 98, (i + 1) * (i + 2)) / (∑ i ∈ range 49, (2 * i + 1) * (2 * i + 3)) = 2 + 2 / 3299 := by
  native_decide