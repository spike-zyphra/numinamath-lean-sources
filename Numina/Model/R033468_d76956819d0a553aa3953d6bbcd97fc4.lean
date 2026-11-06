import Mathlib

open Real Set
open scoped BigOperators

open Polynomial

theorem algebra_9017 (f : ℝ → ℝ) (hf : f = λ x => 3 * x - x ^ 3) :
    IsGreatest (image f (Icc 2 3)) (-2) ∧ IsLeast (image f (Icc 2 3)) (-18) := by
  constructor
  · -- Show that -2 is the greatest element in the image
    constructor
    · -- Show that -2 is in the image
      rw [hf]
      simp only [mem_image, mem_setOf_eq, mem_Icc]
      use 2
      norm_num
    · -- Show that -2 is an upper bound
      intro y
      rintro ⟨x, hx, rfl⟩
      rw [hf]
      simp at *
      have h1 : 2 ≤ x := by linarith [hx.1]
      have h2 : x ≤ 3 := by linarith [hx.2]
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 1), sq_nonneg (x - 3), sq_nonneg (x - 2), mul_nonneg (show 0 ≤ x - 2 by nlinarith) (show 0 ≤ (x + 1) by nlinarith)]
  · -- Show that -18 is the least element in the image
    constructor
    · -- Show that -18 is in the image
      rw [hf]
      simp only [mem_image, mem_setOf_eq, mem_Icc]
      use 3
      norm_num
    · -- Show that -18 is a lower bound
      intro y
      rintro ⟨x, hx, rfl⟩
      rw [hf]
      simp at *
      have h1 : 2 ≤ x := by linarith [hx.1]
      have h2 : x ≤ 3 := by linarith [hx.2]
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3), sq_nonneg (x + 1), sq_nonneg (x - 3), mul_nonneg (show 0 ≤ 3 - x by nlinarith) (show 0 ≤ (x + 1) by nlinarith)]