import Mathlib

open Finset Real

theorem inequalities_4841 {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ)
    (h₁ : IsLeast {y | ∃ i ∈ Icc 1 n, x i = y} (x 1))
    (h₂ : IsGreatest {y | ∃ i ∈ Icc 1 n, x i = y} (x n))
    (h₃ : ∑ i ∈ Icc 1 n, x i = 0) :
    ∑ i ∈ Icc 1 n, (x i) ^ 2 + n * x 1 * x n ≤ 0 := by
  -- Prove that x1 ≤ xi for all i ∈ Icc 1 n
  have h4 : ∀ y, y ∈ {y | ∃ i ∈ Icc 1 n, x i = y} → x 1 ≤ y := by 
    apply h₁.2
  -- Prove that xi ≤ xn for all i ∈ Icc 1 n
  have h5 : ∀ y, y ∈ {y | ∃ i ∈ Icc 1 n, x i = y} → y ≤ x n := by 
    apply h₂.2
  -- For all i, x1 ≤ x i
  have h6 : ∀ i ∈ Icc 1 n, x 1 ≤ x i := by
    intro i hi
    have h7 : x i ∈ {y | ∃ i ∈ Icc 1 n, x i = y} := by 
      refine ⟨i, hi, rfl⟩
    have h8 : x 1 ≤ x i := h4 (x i) h7
    linarith
  -- For all i, x i ≤ xn
  have h7 : ∀ i ∈ Icc 1 n, x i ≤ x n := by 
    intro i hi
    have h7 : x i ∈ {y | ∃ i ∈ Icc 1 n, x i = y} := by 
      refine ⟨i, hi, rfl⟩
    have h8 : x i ≤ x n := h5 (x i) h7
    linarith
  -- For each i, (x i)^2 + x 1 * x n ≤ (x 1 + x n) * (x i)
  have h8 : ∀ i ∈ Icc 1 n, (x i) ^ 2 + x 1 * x n ≤ (x 1 + x n) * (x i) := by 
    intro i hi
    have h6' : x 1 ≤ x i := h6 i hi
    have h7' : x i ≤ x n := h7 i hi
    nlinarith [sq_nonneg (x i - x 1), sq_nonneg (x i - x n), sq_nonneg (x 1 - x n)]
  -- Sum both sides over i ∈ Icc 1 n
  have h9 : ∑ i ∈ Icc 1 n, ((x i) ^ 2 + x 1 * x n) ≤ ∑ i ∈ Icc 1 n, ((x 1 + x n) * (x i)) := by 
    apply Finset.sum_le_sum 
    intro i hi
    exact h8 i hi
  -- The right side sum is (x 1 + x n) * (∑ i ∈ Icc 1 n, (x i))
  have h10 : ∑ i ∈ Icc 1 n, ((x 1 + x n) * (x i)) = (x 1 + x n) * (∑ i ∈ Icc 1 n, (x i)) := by 
    simp [Finset.mul_sum]
  -- Since ∑ i ∈ Icc 1 n, (x i) = 0, the right side is 0
  rw [h₃] at h10
  have h11 : ∑ i ∈ Icc 1 n, ((x 1 + x n) * (x i)) = 0 := by
    linarith
  -- The left side sum is ∑ i ∈ Icc 1 n, (x i) ^ 2 + n * x 1 * x n
  have h12 : ∑ i ∈ Icc 1 n, ((x i) ^ 2 + x 1 * x n) = ∑ i ∈ Icc 1 n, (x i) ^ 2 + n * (x 1 * x n) := by 
    rw [Finset.sum_add_distrib]
    simp
    <;> ring
  -- Combining left and right sides
  have h13 : ∑ i ∈ Icc 1 n, ((x i) ^ 2 + x 1 * x n) ≤ (0 : ℝ) := by 
    linarith [h9, h11]
  -- Final step: rearranging
  linarith [h12, h13]