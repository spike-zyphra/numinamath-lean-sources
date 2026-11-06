import Mathlib

theorem algebra_37648 {x y : ℝ} (h1 : y * (x + y)^2 = 2) (h2 : 8 * y * (x^3 - y^3) = 13) :
    (x, y) = (3 / 2, 1 / 2) := by
  have h3 : y ≠ 0 := by
    by_contra h
    rw [h] at h1 h2
    nlinarith
  have h5 : y ^ 3 = 1 / 8 := by
    nlinarith [sq_nonneg (x ^ 2 - 3 / 4), sq_nonneg ((x + y) ^ 2 - 1), sq_nonneg (y ^ 2 - 1 / 4), sq_nonneg (x - 3 / 2), sq_nonneg (y - 1 / 2), sq_pos_of_ne_zero h3, sq_nonneg (x + y - 2), sq_nonneg (x - 3 * y)]
  have h6 : y = 1 / 2 := by
    have h7 : y ^ 3 - 1 / 8 = 0 := by linarith
    have h8 : (y - 1 / 2) * (y ^ 2 + y / 2 + 1 / 4) = 0 := by
      ring_nf at h7 ⊢
      nlinarith
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- Case where y - 1 / 2 = 0 
      linarith
    · -- Case where y ^ 2 + y / 2 + 1 / 4 = 0 
      nlinarith [sq_nonneg (y + 1 / 4), sq_nonneg (y ^ 2)]
  have hx1 : x = 3 / 2 := by
    rw [show y = 1 / 2 by linarith [h6]] at h1
    nlinarith [sq_nonneg (x - 3 / 2), sq_nonneg (x + 5 / 2), sq_nonneg ((x + 1 / 2) ^ 2 - 4), sq_nonneg (x ^ 2 - 9 / 4)]
  simp [hx1, h6]
  all_goals linarith