import Mathlib

open Real

/- 14. Find the value of $\sin \frac{\pi}{7} \sin \frac{2 \pi}{7} \sin \frac{3 \pi}{7}$. -/
theorem algebra_102073 : sin (π / 7) * sin (2 * π / 7) * sin (3 * π / 7) = sqrt 7 / 8 := by
  -- Let t = sin (π / 7) * sin (2 * π / 7) * sin (3 * π / 7)
  set t : ℝ := _ * _ * _
  -- It is enough to show that t^2 = 7/8^2.
  suffices t ^ 2 = 7 / 8 ^ 2 by
    rw [← sq_eq_sq₀ _ (by positivity), this, div_pow, sq_sqrt (by norm_num)]
    -- The result follows from 0 ≤ t.
    apply mul_nonneg <;> [apply mul_nonneg; skip]
    all_goals apply sin_nonneg_of_nonneg_of_le_pi <;> linarith [pi_pos]
  calc
    -- We have t^2 = 1 / 8 * (1 - c(2)) * (1 - c(4)) * (1 - c(6)) where
    -- c(n) = cos(n * π / 7).
    -- sin (n * π / 7) ^ 2 = 1 / 2 * (1 - cos (2 * n * π / 7)) = 1 / 2 * (1 - c(2 * n)).
    t ^ 2 = 1 / 8 * (1 - cos (2 * π / 7)) * (1 - cos (4 * π / 7)) * (1 - cos (6 * π / 7)) := by
      simp_rw [t, mul_pow, sin_sq_eq_half_sub]
      ring_nf
    -- We have
    -- (1 - c(2)) * (1 - c(4)) * (1 - c(6))
    --   = (1 - (c2 + c4 + c6) + 1/2 * (2 * c2 * c4 + 2 * c4 * c6 + 2 * c6 * c2) - c2 * c4 * c6).
    _ = 1 / 8 * (1 - (cos (2 * π / 7) + cos (4 * π / 7) + cos (6 * π / 7))
          + 1 / 2 * (2 * cos (2 * π / 7) * cos (4 * π / 7) + 2 * cos (4 * π / 7) * cos (6 * π / 7) + 2 * cos (6 * π / 7) * cos (2 * π / 7))
          - cos (2 * π / 7) * cos (4 * π / 7) * cos (6 * π / 7)) := by
      ring
    -- c2 + c4 + c6 = c2 - c3 - c1 since c(4) = cos(π - 3 * π / 7) = -cos(3 * π / 7) = c(3).
    -- 2 * c2 * c4 + 2 * c4 * c6 + 2 * c6 * c2
    --   = c6 + c2 + c10 + c2 + c8 + c4
    --   = -c1 + c2 - c3 + c2 - c1 - c3
    --   = 2 * (c2 - c3 - c1).
    -- So we get -(c2 + c4 + c6) - 1/2 * (2 * c2 * c4 + 2 * c4 * c6 + 2 * c6 * c2) - c2 * c4 * c6)
    --    = -(c2 - c3 - c1) + 1/2 * 2 * (c2 - c3 - c1) = 0.
    _ = 1 / 8 * (1 - cos (2 * π / 7) * cos (4 * π / 7) * cos (6 * π / 7)) := by
      simp_rw [two_mul_cos_mul_cos]
      rw [show 2 * π / 7 - 4 * π / 7 = -(2 * π / 7) by ring, cos_neg]
      rw [show 2 * π / 7 + 4 * π / 7 = π - π / 7 by ring, cos_pi_sub]
      rw [show 4 * π / 7 - 6 * π / 7 = -(2 * π / 7) by ring, cos_neg]
      rw [show 4 * π / 7 + 6 * π / 7 = 3 * π / 7 + π by ring, cos_add_pi]
      rw [show 6 * π / 7 - 2 * π / 7 = π - (3 * π / 7) by ring, cos_pi_sub]
      rw [show 6 * π / 7 + 2 * π / 7 = π / 7 + π by ring, cos_add_pi]
      rw [show 4 * π / 7 = π - 3 * π / 7 by ring, cos_pi_sub]
      rw [show 6 * π / 7 = π - π / 7 by ring, cos_pi_sub]
      ring
    -- c2 * c4 * c6 = 8 * sin(2 * π / 7) * c2 * c4 * c6 / (8 * sin(2 * π / 7)).
    _ = 1 / 8 * (1 - 2 * (2 * (2 * sin (2 * π / 7) *  cos (2 * π / 7)) * cos (4 * π / 7)) * cos (6 * π / 7) / (8 * sin (2 * π / 7))) := by
      congr 2
      simp_rw [← mul_assoc, show 2 * 2 * 2 = (8 : ℝ) by norm_num, mul_assoc]
      rw [mul_div_mul_left _ _ (by norm_num), mul_div_cancel_left₀]
      apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi <;> linarith [pi_pos]
    -- 8 * sin (2 π / 7) * c2 * c4 * c6 = 2 * sin (8 * π / 7) * c6
    --    = 2 * -sin (π / 7) * -c1 = sin (2 * π / 7).
    -- So 8 * sin (2 π / 7) * c2 * c4 * c6 / (8 * sin (2 * π / 7)) = 1 / 8.
    _ = 1 / 8 * (1 - 1 / 8) := by
      congr 2
      rw [← sin_two_mul, show 2 * (2 * π / 7) = 4 * π / 7 by ring]
      rw [← sin_two_mul, show 2 * (4 * π / 7) = π / 7 + π by ring]
      rw [show 6 * π / 7 = π - π / 7 by ring]
      rw [sin_add_pi, cos_pi_sub, show ∀ x y : ℝ, 2 * -x * -y = 2 * x * y by intros; ring]
      rw [← sin_two_mul, mul_div, div_mul_cancel_right₀, one_div]
      apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi <;> linarith [pi_pos]
    _ = 7 / 8 ^ 2 := by norm_num