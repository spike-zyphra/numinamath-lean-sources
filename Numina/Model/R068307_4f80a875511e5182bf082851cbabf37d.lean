import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12643 {f : ℝ → ℝ} (hf : ∀ x, x < 0 → f x = 0)
  (hf' : ∀ x, x ≥ 0 → f x = 1) :
  ∀ x, f (f x) = 1 := by 
  intro x 
  by_cases h : x < 0 
  · -- Suppose x < 0
    have hx1 : f x = 0 := hf x h
    rw [hx1]
    norm_num [hf']
  · -- If x ≥ 0 
    have hx2 : f x = 1 := hf' x (by linarith)
    rw [hx2]
    norm_num [hf']