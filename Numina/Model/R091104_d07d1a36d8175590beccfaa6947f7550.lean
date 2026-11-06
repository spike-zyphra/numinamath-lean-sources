import Mathlib

theorem algebra_199618 {A B : ℤ}
    (hA : A = ∑ i ∈ Finset.range 2022, (i + 1) * 2022 + ∑ i ∈ Finset.range 2021, (i + 1) * 2021)
    (hB : B = ∑ i ∈ Finset.range 2022, (2023 - i) * 2022 + ∑ i ∈ Finset.range 2021, (2022 - i) * 2021) :
    A / B = 1 / 2 := by
  rw [hA, hB]
  native_decide