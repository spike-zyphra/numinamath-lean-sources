import Mathlib

theorem algebra_9418 : IsLeast {z | ∃ x y : ℝ, z = x * y ∧ 0 < x ∧ 0 < y ∧
  2 * x + y + 6 = x * y } 18 := by
  constructor
  · -- Show 18 is in the set
    use 3, 6
    norm_num
  · -- Show any element in the set is ≥ 18
    intro z h
    rcases h with ⟨x, y, hxy, hx, hy, h⟩
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 6),
      mul_pos hx hy, sq_nonneg (x * y - 18), sq_nonneg (x - 3), sq_nonneg (y - 6),
        mul_pos (show 0 < x - 0 by linarith) (show 0 < y - 0 by linarith)
    ]