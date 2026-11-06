import Mathlib

theorem algebra_234358 : (∑ i ∈ Finset.range 2018, (1 / (i + 1))) * (∑ i ∈ Finset.range 2019, (1 / (i + 1))) -
    (∑ i ∈ Finset.range 2018, (1 / (i + 1))) * (∑ i ∈ Finset.range 2019, (1 / (i + 1))) = 1 / 2019 := by
  native_decide