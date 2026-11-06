import Mathlib

open Real Set
open scoped Real

theorem algebra_9048 {f : ℝ → ℝ} (hf : f = λ x => cos (2 * x) + 2 * sin x) :
    f (-π / 6) = -1 / 2 ∧ ∀ x, f x ∈ Icc (-3) (3 / 2) := by
  have h1 : f (-π / 6) = -1 / 2 := by
    rw [hf]
    have h2 : cos (2 * (-π / 6)) = 1 / 2 := by
      have h3 : 2 * (-π / 6) = - (π / 3) := by
        ring
      rw [h3]
      have h4 : cos (- (π / 3)) = cos (π / 3) := by
        rw [cos_neg]
      rw [h4]
      norm_num
    have h5 : sin (-π / 6) = -1 / 2 := by 
      have h6 : sin (-π / 6) = - sin (π / 6) := by 
        rw [show -π / 6 = - (π / 6) by ring]
        rw [sin_neg]
      rw [h6]
      norm_num
    simp only [h2, h5]
    all_goals linarith
  have h2' : ∀ x, f x ∈ Icc (-3) (3 / 2) := by 
    intro x 
    rw [hf]
    simp only [Set.mem_Icc]
    have h3 : cos (2 * x) = 1 - 2 * (sin x) ^ 2 := by
      rw [cos_two_mul]
      rw [sin_sq]
      <;> ring
    have h4 : -1 ≤ sin x ∧ sin x ≤ 1 := by
      apply sin_mem_Icc
    have h5 : cos (2 * x) + 2 * sin x = 1 + 2 * sin x - 2 * (sin x) ^ 2 := by
      rw [h3]
      all_goals ring
    rw [h5]
    constructor
    · -- Show that -3 ≤ 1 + 2 * sin x - 2 * (sin x) ^ 2 
      nlinarith [sq_nonneg (sin x - 1 / 2), h4.left, h4.right, sq_nonneg (sin x + 1), sq_nonneg (sin x - 2)]
    · -- Show that 1 + 2 * sin x - 2 * (sin x) ^ 2 ≤ 3 / 2 
      nlinarith [sq_nonneg (sin x - 1 / 2), h4.left, h4.right, sq_nonneg (sin x + 1), sq_nonneg (sin x - 2)]
  constructor
  · -- Show that f(-π / 6) = -1 / 2
    exact h1
  · -- Show that ∀ x, f x ∈ Icc (-3) (3 / 2)
    intro x
    apply h2' x