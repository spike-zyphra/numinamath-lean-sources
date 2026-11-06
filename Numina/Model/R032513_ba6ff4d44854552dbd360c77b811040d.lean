import Mathlib

open Real Set

theorem algebra_268127 :
    IsGreatest {t : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ t = x * y - x ^ 3 * y - x * y ^ 3} (1 / 8) := by
  constructor 
  · -- Show that 1/8 is in the set
    use 1 / 2, 1 / 2
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Verify that with x = y = 1/2, we get 1/8
      norm_num
  · -- Show that 1/8 is greatest in the set
    intro t ht
    rcases ht with ⟨x, y, hx, hy, h_eq⟩
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), 
      sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (y ^ 2 - 1 / 4), 
      sq_nonneg (x * y - 1 / 4), sq_nonneg (x - y), 
      mul_pos hx hy, sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y)
    ]