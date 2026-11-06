import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem inequalities_8526 :
  IsGreatest {l : ℝ | ∀ a b c d : ℝ, a^2 + b^2 + c^2 + d^2 ≥ a * b + l * b * c + c * d} (3 / 2) := by
  constructor
  · -- Show that 3/2 is in the set
    intro a b c d
    nlinarith [sq_nonneg (a - b / 2), sq_nonneg (d - c / 2), sq_nonneg (b - c), sq_nonneg (b + c - 2 * a), sq_nonneg (d - b), sq_nonneg (d - c), sq_nonneg (a - d), sq_nonneg (a + d - (b + c)), sq_nonneg (b - c), sq_nonneg ((a - d) + (b - c) / 2)]
  · -- Show that 3/2 is greatest
    intro l hl
    have h1 := hl 1 2 2 1
    norm_num at h1
    linarith