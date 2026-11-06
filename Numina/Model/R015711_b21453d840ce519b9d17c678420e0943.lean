import Mathlib

theorem algebra_95928 (S : Finset ℝ) (hS : S.card = 10) :
    ∑ x ∈ S, (x + 20) = ∑ x ∈ S, x + 200 := by
  have h1 : ∑ x in S, (x + 20) = ∑ x in S, x + ∑ x in S, (20 : ℝ) := by
    rw [Finset.sum_add_distrib]
  have h2 : ∑ x in S, (20 : ℝ) = 200 := by 
    rw [Finset.sum_const]
    rw [hS]
    norm_num
  rw [h1, h2]