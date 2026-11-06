import Mathlib

theorem algebra_28449 (x : ℝ) :
    ∑ i ∈ Finset.range 21, (x - (2020 - i)) / (i + 1) = ∑ i ∈ Finset.range 21, (x - (i + 1)) / (2020 - i) ↔ x = 2021 := by
  constructor
  · -- (∑ i ∈ Finset.range 21, (x - (2020 - i)) / (i + 1) = ∑ i ∈ Finset.range 21, (x - (i + 1)) / (2020 - i)) → x = 2021
    intro h_eq
    norm_num [Finset.sum_range_succ] at h_eq ⊢
    linarith
  · -- x = 2021 → (∑ i ∈ Finset.range 21, (x - (2020 - i)) / (i + 1) = ∑ i ∈ Finset.range 21, (x - (i + 1)) / (2020 - i))
    intro h_eq
    rw [h_eq]
    norm_num [Finset.sum_range_succ]