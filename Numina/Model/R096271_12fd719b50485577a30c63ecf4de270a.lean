import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_151938 {x y : ℝ} (hx : x = 1) (hy : y = 0) :
    x^(2*y + 1) + (sin y)^(4/3 * sqrt (3*x)) = 1 ∧
    cos y - x = 0 := by
  rw [hx, hy]
  constructor
  · -- Show that 1^(2*0 + 1) + sin(0)^(4/3 * sqrt (3*1)) = 1
    have h1 : (1 : ℝ) ^ (2 * (0 : ℝ) + 1) = 1 := by
      norm_num
    have h2 : (sin (0 : ℝ) : ℝ) ^ (4 / 3 * sqrt (3 * (1 : ℝ))) = 0 := by
      have hsin : sin (0 : ℝ) = 0 := by
        simp
      rw [hsin]
      norm_num
    linarith [h1, h2]
  · -- Show that cos(0) - 1 = 0
    have hcos : cos (0 : ℝ) = 1 := by
      norm_num [cos_zero]
    rw [hcos]
    all_goals norm_num