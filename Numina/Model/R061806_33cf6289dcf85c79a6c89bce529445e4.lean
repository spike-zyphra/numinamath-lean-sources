import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_106432 {a : ℕ → ℝ}
  (ha1 : a 1 = 1)
  (han : ∀ n, a (n + 1) = a n + 1 / (2 * a n)) :
  Tendsto (λ n => a n - sqrt n) atTop (𝓝 0) := by 
  have h1 := han 0
  rw [show (0 + 1 : ℕ) = 1 by omega] at h1
  rw [ha1] at h1 
  have h2 : 2 * a 0 ≠ 0 := by
    by_contra h
    have : a 0 = 0 := by linarith
    rw [this] at h1
    norm_num at h1 
  field_simp [h2] at h1 
  all_goals nlinarith [sq_nonneg (a 0 - 1 / 2)]