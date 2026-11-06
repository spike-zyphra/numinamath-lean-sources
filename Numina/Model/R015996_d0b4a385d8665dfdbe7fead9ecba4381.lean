import Mathlib

theorem algebra_244364 (n : ℤ) (h : ∑ i ∈ Finset.range 2019, (n + i) = 2019) :
    ∏ i ∈ Finset.range 2019, (n + i) = 0 := by
  have h1 : n = -1008 := by
    have h2 : ∑ i in Finset.range 2019, (n + i) = 2019 * n + (2018 * 2019 / 2 : ℤ) := by 
      rw [Finset.sum_add_distrib]
      have h3 : ∑ i in Finset.range 2019, (n : ℤ) = 2019 * n := by
        simp
      have h4 : ∑ i in Finset.range 2019, (i : ℤ) = (2018 * 2019 / 2 : ℤ) := by
        native_decide
      rw [h3, h4]
    rw [h2] at h
    omega
  rw [h1]
  native_decide