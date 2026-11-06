import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_231329 {k n : ℕ} (hn : 0 < n) (α : ℂ) (hα : α = 2 * Real.cos (k * Real.pi / n)) :
    α.im = 0 := by
  rw [hα]
  simp [Complex.mul_im, Complex.ofReal_im, Real.cos]
  all_goals norm_num