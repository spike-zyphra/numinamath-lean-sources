import Mathlib

theorem algebra_308948 {a b : ℝ} (ha : a^2 + (Real.sqrt Real.pi)^4 = 2 * (Real.sqrt Real.pi)^2 * a + 1)
    (hb : b^2 + (Real.sqrt Real.pi)^4 = 2 * (Real.sqrt Real.pi)^2 * b + 1) (hne : a ≠ b) :
    |a - b| = 2 := by
  have h1 : a^2 - b^2 = 2 * (Real.sqrt Real.pi) ^ 2 * (a - b) := by
    have eq1 : a^2 + (Real.sqrt Real.pi) ^ 4 = 2 * (Real.sqrt Real.pi) ^ 2 * a + 1 := by
      linarith [ha]
    have eq2 : b^2 + (Real.sqrt Real.pi) ^ 4 = 2 * (Real.sqrt Real.pi) ^ 2 * b + 1 := by
      linarith [hb]
    nlinarith [eq1, eq2]
  have h2 : a + b = 2 * (Real.sqrt Real.pi) ^ 2 := by
    have h3 : a - b ≠ 0 := by
      intro h
      apply hne
      linarith
    apply (mul_left_inj' h3).mp
    linarith [h1]
  have h3 : (a - b) ^ 2 = 4 := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
      by_contra h
      apply hne
      linarith
    ), Real.sq_sqrt (show (0 : ℝ) ≤ Real.pi by linarith [Real.pi_pos]), Real.sqrt_pos.mpr (show (0 : ℝ) < Real.pi by linarith [Real.pi_pos]), sq_nonneg (a + b - 2 * (Real.sqrt Real.pi) ^ 2), sq_nonneg (a - b)]
  have h4 : |a - b| = 2 := by
    have h6 : (a - b) ^ 2 = 4 := h3
    have h7 : |a - b| = 2 := by
      have h8 : |a - b| = Real.sqrt ((a - b) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h8, h6]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact h7
  exact h4