import Mathlib

theorem algebra_3507 :
  IsLeast {n : ℝ | ∃ x y : ℝ, n = 2 * x ^ 2 + 2 * x * y + y ^ 2 + 2 * x} (-1) := by
  constructor
  · -- Show that -1 is achievable
    use -1, 1
    norm_num
  · -- Show that -1 is the smallest value
    intro n hn
    rcases hn with ⟨x, y, h⟩
    have h1 : 2 * x ^ 2 + 2 * x * y + y ^ 2 + 2 * x ≥ -1 := by
      nlinarith [sq_nonneg (x + y / 2 + 1 / 2), sq_nonneg (y - 1)]
    linarith [h, h1]