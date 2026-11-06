import Mathlib

theorem number_theory_203095 (S : Finset ℚ) (hS : S = {1/2, 1/4, 1/6, 1/8, 1/10, 1/12}) :
    ∃ T ⊆ S, ∑ x ∈ T, x = 1 ∧ ∏ x ∈ S \ T, x = 1/80 := by 
  use {1/2, 1/4, 1/6, 1/12}
  constructor
  · -- Show {1/2, 1/4, 1/6, 1/12} ⊆ S
    rw [hS]
    native_decide 
  constructor
  · -- Show sum is 1
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  · -- Show product is 1/80
    rw [hS]
    native_decide