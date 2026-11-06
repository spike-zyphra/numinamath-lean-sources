import Mathlib

theorem algebra_164351 {a b c x : ℝ} (h : (a + b) * (b + c) * (c + a) ≠ 0)
    (h1 : a^2 / (a + b) = a^2 / (a + c) + 20) (h2 : b^2 / (b + c) = b^2 / (b + a) + 14)
    (h3 : c^2 / (c + a) = c^2 / (c + b) + x) :
    x = -34 := by
  have ha1 : a + b ≠ 0 := by
    intro h11
    have : (a + b) * (b + c) * (c + a) = 0 := by
      rw [show a + b = 0 by linarith]
      norm_num
    contradiction
  have ha2 : a + c ≠ 0 := by
    intro h11
    have : (a + b) * (b + c) * (c + a) = 0 := by
      rw [show c + a = 0 by linarith]
      norm_num
    contradiction
  have hb1 : b + c ≠ 0 := by
    intro h11
    have : (a + b) * (b + c) * (c + a) = 0 := by
      rw [show b + c = 0 by linarith]
      norm_num
    contradiction
  have hb2 : b + a ≠ 0 := by
    intro h11
    have : (a + b) * (b + c) * (c + a) = 0 := by
      have h12 : a + b = 0 := by linarith
      rw [show a + b = 0 by linarith]
      norm_num
    contradiction
  have hc1 : c + a ≠ 0 := by
    intro h11
    have : (a + b) * (b + c) * (c + a) = 0 := by
      rw [show c + a = 0 by linarith]
      norm_num
    contradiction
  have hc2 : c + b ≠ 0 := by
    intro h11
    have : (a + b) * (b + c) * (c + a) = 0 := by
      rw [show b + c = 0 by linarith]
      norm_num
    contradiction
  have eq1 : a^2 * (a + c) = a^2 * (a + b) + 20 * (a + b) * (a + c) := by
    have h11 : a + b ≠ 0 := ha1
    have h12 : a + c ≠ 0 := ha2
    field_simp [h11, h12] at h1
    nlinarith
  have eq2 : b^2 * (b + a) = b^2 * (b + c) + 14 * (b + c) * (b + a) := by
    have h21 : b + c ≠ 0 := hb1
    have h22 : b + a ≠ 0 := hb2
    field_simp [h21, h22] at h2
    nlinarith
  have eq3 : c^2 * (c + b) = c^2 * (c + a) + x * (c + a) * (c + b) := by
    have h31 : c + a ≠ 0 := hc1
    have h32 : c + b ≠ 0 := hc2
    field_simp [h31, h32] at h3
    nlinarith
  -- Now, we need to solve for x.
  have h4 : x = -34 := by
    apply (mul_left_inj' (show (c + a) * (c + b) ≠ 0 by
      -- We know from assumptions
      have h1 : c + a ≠ 0 := hc1
      have h2 : c + b ≠ 0 := hc2
      exact mul_ne_zero h1 h2
    )).mp
    -- Now, we can rewrite eq3
    nlinarith [sq_pos_of_ne_zero (show a + b ≠ 0 by exact ha1), sq_pos_of_ne_zero (show b + c ≠ 0 by exact hb1), sq_pos_of_ne_zero (show c + a ≠ 0 by exact hc1), sq_pos_of_ne_zero (show b + a ≠ 0 by exact hb2), sq_pos_of_ne_zero (show c + a ≠ 0 by exact hc1), sq_pos_of_ne_zero (show c + b ≠ 0 by exact hc2), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  -- Now, we conclude with the value of x.
  linarith