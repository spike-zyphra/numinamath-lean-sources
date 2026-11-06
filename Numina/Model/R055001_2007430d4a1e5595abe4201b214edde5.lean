import Mathlib

theorem algebra_12981 :
    IsLeast {t : ℝ | ∃ x y, t = 2 * x ^ 2 + 4 * x * y + 3 * y ^ 2 + 6 * y + 4} (-5) := by
  constructor
  · -- Show that -5 is achievable
    use 3, -3
    norm_num
  · -- Show that -5 is the minimum value
    intro t ht
    rcases ht with ⟨x, y, ht⟩
    have h1 : 2 * x ^ 2 + 4 * x * y + 3 * y ^ 2 + 6 * y + 4 ≥ -5 := by
      nlinarith [sq_nonneg (x + y), sq_nonneg (y + 3)]
    linarith [ht, h1]