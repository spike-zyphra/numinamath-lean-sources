import Mathlib

theorem algebra_2872 : IsLeast {t : ℝ | ∃ x y, t = 5 * x ^ 2 - 8 * x * y + 5 * y ^ 2 - 12 * x + 6 * y + 2022} 2013 := by
  constructor
  · -- First, show that 2013 is in the set.
    use 2, 1
    norm_num
  · -- Show that 2013 is the least element in the set (minimum).
    intro t ht
    rcases ht with ⟨x, y, ht_eq⟩
    have h1 : 5 * x ^ 2 - 8 * x * y + 5 * y ^ 2 - 12 * x + 6 * y + 2022 ≥ 2013 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (x - 4 / 5 * y - 6 / 5), sq_nonneg (y - 1)]
    linarith