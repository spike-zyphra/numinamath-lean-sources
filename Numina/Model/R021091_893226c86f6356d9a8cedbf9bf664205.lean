import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_306012 {n : ℕ} (hn : 3 ≤ n) (x : Fin n → ℝ)
  (hx : ∀ i, x i ∈ Icc (-1) 1) (h : ∑ i, (x i)^3 = 0) :
  ∑ i, x i ≤ n / 3 := by
  have h1 : ∀ i, 4 * (x i) ^ 3 ≥ 3 * (x i) - 1 := by
    intro i
    have h2 : -1 ≤ x i := by
      have h3 : x i ∈ Icc (-1 : ℝ) 1 := hx i
      exact h3.1
    have h3 : x i ≤ 1 := by
      have h4 : x i ∈ Icc (-1 : ℝ) 1 := hx i
      exact h4.2
    nlinarith [sq_nonneg ((x i) ^ 2 - 1 / 4), sq_nonneg ((x i) + 1), sq_nonneg ((x i) - 1 / 2), sq_nonneg ((x i) - 1), sq_nonneg ((x i) ^ 2 - (x i)), sq_nonneg ((x i) ^ 2 - 2 * (x i) + 1), sq_nonneg ((x i) + 1), mul_nonneg (show (0 : ℝ) ≤ 1 + (x i) by linarith) (show (0 : ℝ) ≤ 1 - (x i) by linarith)]
  have h2 : 4 * (∑ i, (x i) ^ 3) ≥ 3 * (∑ i, (x i)) - (↑n : ℝ) := by
    calc
      4 * (∑ i, (x i) ^ 3) = ∑ i, (4 * ((x i) ^ 3)) := by
        simp [Finset.mul_sum]
      _ ≥ ∑ i, (3 * (x i) - 1) := by
        apply Finset.sum_le_sum
        intro i _
        have h3 : 4 * ((x i) ^ 3) ≥ 3 * (x i) - 1 := h1 i
        linarith
      _ = 3 * (∑ i, (x i)) - (↑n : ℝ) := by
        calc
          ∑ i, (3 * (x i) - 1) = ∑ i, (3 * (x i)) - ∑ i, (1 : ℝ) := by
            rw [Finset.sum_sub_distrib]
          _ = 3 * (∑ i, (x i)) - (↑n : ℝ) := by
            have h3 : ∑ i, (3 * (x i)) = 3 * (∑ i, (x i)) := by
              simp [Finset.mul_sum]
            have h4 : ∑ i : Fin n, (1 : ℝ) = (↑n : ℝ) := by
              simp
            rw [h3, h4]
  have h3 : 0 ≥ 3 * (∑ i, (x i)) - (↑n : ℝ) := by
    have h4 : 4 * (∑ i, (x i) ^ 3) ≥ 3 * (∑ i, (x i)) - (↑n : ℝ) := h2
    have h5 : 4 * (∑ i, (x i) ^ 3) = 0 := by
      rw [h]
      norm_num
    linarith
  have h4 : 3 * (∑ i, (x i)) ≤ (↑n : ℝ) := by
    linarith
  have h5 : (∑ i, (x i)) ≤ (↑n / 3 : ℝ) := by
    linarith
  simpa using h5