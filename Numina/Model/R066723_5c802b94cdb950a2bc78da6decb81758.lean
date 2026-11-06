import Mathlib

theorem algebra_280863 (t : ℝ) (ht : t = 3) :
    dist (5 * t) (15 * t - 70) = 10 ∨
    dist (5 * t) (15 * t - 70) = 40 ∨
    dist (5 * t) (15 * t - 70) = 100 ∨
    dist (5 * t) (15 * t - 70) = 130 := by
  rw [ht]
  norm_num [dist]
  all_goals norm_num
  <;> tauto