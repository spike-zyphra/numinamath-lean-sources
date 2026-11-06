import Mathlib

theorem algebra_2035 {x y : ℝ} (hx1 : x * (x + y) ^ 2 = 9) (hx2 : x * (x ^ 3 - y ^ 3) = -7) :
    x = 1 ∧ y = 2 := by
  have h4 : x ≠ 0 := by
    by_contra h
    rw [h] at hx1 hx2
    nlinarith
  have h3 : y = 2 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 2), sq_nonneg (x + y - 3),
          sq_nonneg (x * (x + y)), sq_nonneg (x * (x - y)), sq_pos_of_ne_zero (show x ≠ 0 by assumption), sq_nonneg (y + 2)]
  have hx3 : x = 1 := by
    rw [show y = 2 by linarith [h3]] at hx1 hx2
    nlinarith
  constructor
  · linarith
  · linarith