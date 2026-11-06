import Mathlib

theorem algebra_12125 : IsGreatest {t : ℝ | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ 4 * x + 9 * y = 60 ∧ x * y = t} 25 := by
  constructor
  · -- Show 25 is achievable
    use 15 / 2, 10 / 3
    constructor
    · norm_num -- Show 0 < 15/2
    constructor
    · norm_num -- Show 0 < 10/3
    constructor
    · norm_num -- Show 4 * (15/2) + 9 * (10/3) = 60
    · norm_num -- Show (15/2) * (10/3) = 25
  · -- Show 25 is the greatest
    intro t ht
    rcases ht with ⟨x, y, hx, hy, h, ht⟩
    nlinarith [sq_nonneg (x - 15 / 2), sq_nonneg (y - 10 / 3), sq_nonneg (4 * x - 30), sq_nonneg (9 * y - 30),
      mul_pos hx hy, sq_nonneg (x * y - 25), sq_nonneg (4 * x + 9 * y - 60)
      ]