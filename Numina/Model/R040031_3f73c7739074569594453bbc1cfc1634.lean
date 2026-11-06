import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_141164 : IsGreatest {V : ℝ | ∃ x, 0 < x ∧ x < 14 / 2 ∧ (x * (14 - 2 * x) * (30 - 2 * x)) = V} 576 := by
  constructor
  · -- Show that 576 is achievable with x = 3
    use 3
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that no greater value is achievable
    intro V h
    rcases h with ⟨x, hx1, hx2, hV⟩
    nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 5), sq_nonneg (x - 2), sq_nonneg (x * (x - 3)), sq_nonneg ((14 - 2 * x) - 8), sq_nonneg ((30 - 2 * x) - 24), mul_pos hx1 (show 0 < (14 / 2 - x) by linarith)]