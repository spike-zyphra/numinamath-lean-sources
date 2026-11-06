import Mathlib

theorem algebra_878 {x y : ℝ} (h1 : x - y ^ 2 + y ^ 3 = y ^ 4) (h2 : y - x ^ 2 + x ^ 3 = x ^ 4) : (x, y) = (0, 0) ∨ (x, y) = (1, 1) := by
  have h3 : (x - y) * (1 + (x + y) - (x ^ 2 + x * y + y ^ 2)) = - (x - y) * (x + y) * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  by_cases h5 : x = y
  · -- x = y
    have h4 : x = y := h5
    have h6 : x ^ 4 - x ^ 3 + x ^ 2 - x = 0 := by
      have eq1 : x - x ^ 2 + x ^ 3 = x ^ 4 := by
        have h1' : x - y ^ 2 + y ^ 3 = y ^ 4 := h1
        rw [show y = x by linarith [h4]] at h1'
        nlinarith
      nlinarith
    have h7 : x * (x - 1) * (x ^ 2 + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · cases' (mul_eq_zero.mp h8) with h10 h11
      · -- x = 0
        have hx0 : x = 0 := by linarith
        have hy0 : y = 0 := by linarith [h4, hx0]
        left
        simp [hx0, hy0]
      · -- x - 1 = 0
        have hx1 : x = 1 := by linarith
        have hy1 : y = 1 := by linarith [h4, hx1]
        right
        simp [hx1, hy1]
    · -- x^2 + 1 = 0
      have h10 : x ^ 2 + 1 > 0 := by
        nlinarith [sq_nonneg x]
      have h11 : x ^ 2 + 1 = 0 := by nlinarith
      nlinarith [sq_nonneg x]
  · -- x ≠ y
    have h5' : x ≠ y := h5
    have h8 : (x - y) ≠ 0 := by
      intro h
      apply h5
      linarith
    have h9 : 1 + (x + y) - (x ^ 2 + x * y + y ^ 2) = - (x + y) * (x ^ 2 + y ^ 2) := by
      apply (mul_left_inj' h8).mp
      linarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y - 1 / 4), sq_pos_of_ne_zero (show x - y ≠ 0 by exact h8)]