import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_11932 {v w : ℝ × ℝ × ℝ}
  (hw : w ≠ 0) (h : v • w = 1 * w • w + 0 * w • w + (-3) * w • w) :
  (-2 * v) • w = (-2) * w • w + 0 * w • w + 6 * w • w := by
  have h1 : (-2 * v) • w = -2 * (v • w) := by
    simp [Finset.sum_mul, mul_add, add_mul, mul_assoc]
    <;> ring
  rw [h1]
  rw [h]
  all_goals ring