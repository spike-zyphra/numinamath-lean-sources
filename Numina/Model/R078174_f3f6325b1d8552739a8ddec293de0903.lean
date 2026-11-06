import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_292342 :
  IsLeast {s : ℝ | ∃ x y : ℝ, s = 2 * x ^ 2 - x * y + y ^ 2 + 2 * x + 3 * y} (-4) := by
  constructor
  · -- Let $x=-1, y=-2$, then $S=-4$.
    use -1, -2
    norm_num
  · -- For any real numbers $x, y$, $S \geq -4$.
    rintro s ⟨x, y, hxy⟩
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 2), sq_nonneg (x + 1 - (y + 2) / 4), sq_nonneg ( (y + 2) ), sq_nonneg (x - y )
    ]