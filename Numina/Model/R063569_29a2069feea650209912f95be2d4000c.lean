import Mathlib

theorem algebra_260191 (group1 group2 : Fin 15 → ℤ)
    (hgroup1 : ∀ i, group1 i = ∑ j ∈ Finset.range 10, (i + 1) * (2 * j + 2))
    (hgroup2 : ∀ i, group2 i = ∑ j ∈ Finset.range 10, (i + 1) * (2 * j + 1)) :
    (∑ i ∈ Finset.range 15, group1 i) / (∑ i ∈ Finset.range 15, group2 i) = 160 / 151 := by 
  norm_num [Finset.sum_range_succ, hgroup1, hgroup2]
  <;> native_decide