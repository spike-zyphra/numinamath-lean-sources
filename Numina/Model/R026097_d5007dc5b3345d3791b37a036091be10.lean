import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11524 {f : ℝ → ℝ} (hf : ∀ x ∈ Icc (-1) 1, f x ≥ 0)
  (f_def : ∀ x, f x = 4 * x ^ 3 + b * x + 1) :
  b = -3 := by
  have h1 := hf 1 (by norm_num)
  rw [f_def] at h1
  have h2 := hf (-1) (by norm_num)
  rw [f_def] at h2
  have h3 := hf (1 / 2) (by norm_num)
  rw [f_def] at h3
  have h4 := hf (-1 / 2) (by norm_num)
  rw [f_def] at h4
  norm_num at h1 h2 h3 h4
  linarith