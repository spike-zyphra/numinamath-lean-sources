import Mathlib

theorem algebra_326
    (A B : Finset ℝ)
    (hA : A = {0.28, 3, 7 / 5, 11.32})
    (hB : B = {0.17, 2.23, 3 / 5}) :
    ∑ a ∈ A, ∑ b ∈ B, a * b = 48 := by 
  rw [hA, hB]
  norm_num [Finset.sum_insert, Finset.sum_singleton]