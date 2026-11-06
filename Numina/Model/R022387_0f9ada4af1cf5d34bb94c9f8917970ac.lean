import Mathlib

theorem algebra_187897 (S : Finset ℤ) (hS : S = {2, 4, 6, 8, 10, 12}) :
    ∑ x ∈ S, (1 : ℚ)/x = 1 ↔ (1 : ℚ)/4 + (1 : ℚ)/12 = 1 := by
  rw [hS]
  norm_num [Finset.sum_insert, Finset.sum_singleton]