import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_320565 {f : ℝ → ℝ} (hf : ∀ x y, f ((x + y) / 2) ≤ (f x + f y) / 2) :
    ∀ m, (∀ x, f x = m * x ^ 2 + x) → m ≥ 0 := by
  intro m hm
  have h1 := hf (-1) (1)
  have h2 : f ((-1 + (1 : ℝ)) / 2) = f 0 := by
    norm_num
  have h3 : f 0 = 0 := by
    rw [hm 0]
    norm_num
  have h4 : (f (-1) + f 1) / 2 = m := by
    have h5 : f (-1) = m * ((-1 : ℝ) ) ^ 2 + (-1) := by
      apply hm
    have h6 : f 1 = m * (1 : ℝ) ^ 2 + (1: ℝ) := by
      apply hm
    rw [h5, h6]
    ring
  rw [show (-1 + (1 : ℝ)) / 2 = (0 : ℝ) by norm_num] at h1
  rw [h3] at h1
  linarith [h1, h4]