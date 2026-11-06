import Mathlib

theorem algebra_12625 : ¬ (∀ x : ℝ, 0 < x ^ 2) ↔
    ∃ x : ℝ, ¬ 0 < x ^ 2 := by
  apply not_forall.trans
  simp