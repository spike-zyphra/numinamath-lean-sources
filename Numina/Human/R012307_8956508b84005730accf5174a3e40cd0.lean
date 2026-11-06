import Mathlib
import Mathlib.Order.Basic
import Mathlib.Data.Set.Defs
open Set

/- What is the smallest integer $n$ such that $5n + 3 > -10$? -/

theorem algebra_20533 : IsLeast {n : ℤ | 5 * n + 3 > -10} (-2) := by
  unfold IsLeast
  constructor
  -- show that -2 satisfies the condition
  . simp
  . unfold lowerBounds
    simp
    intros a
    -- proof by contrapositive, if a < -2, then 5 * a + 3 <= -10
    rw [<- Decidable.not_imp_not]
    simp
    intro h
    linarith
