import Mathlib

theorem algebra_128899 (S : Finset ℝ) (hS : S.card = 70)
    (hS1 : ∑ x ∈ S, (x + 4)^2 = ∑ x ∈ S, x^2) :
    ∑ x ∈ S, (x + 5)^2 - ∑ x ∈ S, x^2 = 350 := by
  have eq1 : ∑ x in S, (x + 4) ^ 2 = ∑ x in S, x^2 := hS1
  have eq2 : ∑ x in S, (x + 4) ^ 2 = ∑ x in S, x^2 + 8 * (∑ x in S, x) + 16 * (S.card) := by 
    have h2 : ∑ x in S, (x + 4) ^ 2 = ∑ x in S, (x ^ 2 + 8 * x + 16) := by 
      congr
      funext x
      ring
    rw [h2]
    have h3 : ∑ x in S, (x ^ 2 + 8 * x + 16) = ∑ x in S, x ^ 2 + 8 * (∑ x in S, x) + 16 * (S.card) := by
      have h4 : ∑ x in S, (x ^ 2 + 8 * x + 16) = ∑ x in S, (x ^ 2) + ∑ x in S, (8 * x) + ∑ x in S, (16 : ℝ) := by 
        simp [Finset.sum_add_distrib]
      have h5 : ∑ x in S, (8 * x) = 8 * (∑ x in S, x) := by
        simp [Finset.mul_sum]
      have h6 : ∑ x in S, (16 : ℝ) = 16 * (S.card) := by
        simp [Finset.sum_const, mul_comm]
      rw [h4, h5, h6]
    rw [h3]
  rw [eq2] at eq1
  have eq3 : 8 * (∑ x in S, x) + 16 * (S.card) = 0 := by 
    linarith
  have h2 : ∑ x in S, x = -140 := by
    rw [hS] at eq3
    norm_num at eq3
    linarith
  have eq4 : ∑ x in S, (x + 5) ^ 2 = ∑ x in S, x^2 + 10 * (∑ x in S, x) + 25 * (S.card) := by
    have h4 : ∑ x in S, (x + 5) ^ 2 = ∑ x in S, (x ^ 2 + 10 * x + 25) := by 
      congr
      funext x
      ring
    rw [h4]
    have h5 : ∑ x in S, (x ^ 2 + 10 * x + 25) = ∑ x in S, x ^ 2 + 10 * (∑ x in S, x) + 25 * (S.card) := by
      have h6 : ∑ x in S, (x ^ 2 + 10 * x + 25) = ∑ x in S, (x ^ 2) + ∑ x in S, (10 * x) + ∑ x in S, (25 : ℝ) := by 
        simp [Finset.sum_add_distrib]
      have h7 : ∑ x in S, (10 * x) = 10 * (∑ x in S, x) := by
        simp [Finset.mul_sum]
      have h8 : ∑ x in S, (25 : ℝ) = 25 * (S.card) := by 
        simp [Finset.sum_const, mul_comm]
      rw [h6, h7, h8]
    rw [h5]
  have eq5 : ∑ x in S, (x + 5) ^ 2 - ∑ x in S, x^2 = 10 * (∑ x in S, x) + 25 * (S.card) := by
    linarith [eq4]
  rw [eq5]
  rw [h2]
  rw [hS]
  all_goals norm_num