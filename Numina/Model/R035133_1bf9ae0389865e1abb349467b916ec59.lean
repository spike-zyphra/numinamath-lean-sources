import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_21689 :
  (MeasureTheory.volume {z : ℂ | abs (z - 7 + 10 * .I) ≤ 5}).toReal = 25 * Real.pi := by
  have h2 : {z : ℂ | abs (z - 7 + 10 * Complex.I) ≤ 5} = closedBall (7 - 10 * Complex.I) 5 := by
    ext z
    simp [Complex.abs, Complex.normSq, dist_eq_norm, Complex.normSq]
    all_goals
      norm_num [Complex.normSq]
      <;> ring_nf <;> norm_num
  rw [h2]
  rw [Complex.volume_closedBall]
  all_goals
    ring_nf
    <;> norm_num
  all_goals
    ring