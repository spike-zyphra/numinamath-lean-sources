import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_315360 :
  IsGreatest {u | ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 2 * x + y = 6 ∧ u = 4 * x ^ 2 + 3 * x * y + y ^ 2 - 6 * x - 3 * y} 18 := by
  constructor
  · -- Show that 18 is in the set.
    use 0, 6
    norm_num
  · -- Show that 18 is an upper bound.
    intro u h
    rcases h with ⟨x, y, hx, hy, h_eq, hu⟩
    have h1 : y = 6 - 2 * x := by linarith
    rw [h1] at hu
    nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 3), sq_nonneg (x - 3 / 2), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y - 3)]