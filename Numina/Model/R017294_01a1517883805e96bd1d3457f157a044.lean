import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_163729 {f : ℝ → ℝ} (hf : Monotone f)
  (hadd : ∀ x y, f (x + y) = f x + f y) (hf1 : f 1 = -1)
  (k : ℝ) :
  (∀ t > 0, f (k * logb 2 t) + f (logb 2 t - logb 2 t ^ 2 - 2) > 0) ↔
  k ∈ Ioo (-1 - 2 * sqrt 2) (-1 + 2 * sqrt 2) := by

  have f0 : f 0 = 0 := by
    have h := hadd 0 0
    norm_num at h
    linarith

  have h1 : f 0 ≤ f 1 := by
    apply hf
    all_goals norm_num

  rw [f0, hf1] at h1
  all_goals nlinarith