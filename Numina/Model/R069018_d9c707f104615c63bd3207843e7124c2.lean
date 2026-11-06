import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_186949 {σ : ℝ} {R : ℝ} (hσ : σ > 0) (hR : R > 0)
  (h : σ / (2 * π * R) = 1 / (2 * π * ε0)) :
  σ / (2 * π * R) = 1 / (2 * π * ε0) := by 
  exact h