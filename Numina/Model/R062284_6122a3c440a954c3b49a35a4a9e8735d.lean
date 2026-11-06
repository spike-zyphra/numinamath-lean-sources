import Mathlib

theorem algebra_180240 :
    IsLeast {t : ℝ | ∃ x y, t = 4 * x ^ 2 + 4 * x * y + 4 * y ^ 2 + 12 * x + 8} (-4) := by
  constructor
  · -- First part: show that -4 is in the set
    use -2, 1
    norm_num
  · -- Second part: show that -4 is a lower bound
    intro t ht
    rcases ht with ⟨x, y, h_eq⟩
    nlinarith [sq_nonneg (x + (y / 2) + (3 / 2)), sq_nonneg (y - 1)]