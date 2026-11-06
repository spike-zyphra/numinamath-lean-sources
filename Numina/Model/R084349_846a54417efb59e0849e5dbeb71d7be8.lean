import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_170461 {y : ℝ → ℝ}
  (hy : y = λ x => sqrt (4 * x - x ^ 2) / logb 3 (abs (x - 4))) :
  ∀ x, x ∈ Ico 0 3 ∪ Ioo 3 4 → y x = sqrt (4 * x - x ^ 2) / logb 3 (abs (x - 4)) := by
    intro x hx
    rcases hx with (hx | hx)
    · -- Case x ∈ [0, 3)
      rw [hy]
    · -- Case x ∈ (3, 4)
      rw [hy]