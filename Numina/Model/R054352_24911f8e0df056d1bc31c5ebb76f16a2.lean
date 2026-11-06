import Mathlib

theorem algebra_314008 {a : ℝ} (ha : a = Real.sqrt 5 - 1) :
    2*a^3 + 7*a^2 - 2*a - 12 = 0 := by
  have h1 : a + 1 = Real.sqrt 5 := by
    rw [ha]
    ring
  have h2 : (a + 1) ^ 2 = 5 := by
    rw [h1]
    rw [Real.sq_sqrt]
    all_goals norm_num
  have h3 : a^2 + 2*a - 4 = 0 := by
    nlinarith
  have h4 : a^3 = 8*a - 8 := by
    have ha2 : a^2 = -2*a +4 := by linarith
    calc
      a^3 = a * a^2 := by ring
      _ = a * (-2*a +4) := by rw [ha2]
      _ = -2*a^2 +4*a := by ring
      _ = -2*(-2*a +4) +4*a := by rw [ha2]
      _ = 8*a -8 := by ring
  -- Now that we have expressions for a^3 and a^2, we can compute the original polynomial.
  rw [h4]
  have ha2_subst : a^2 = -2*a +4 := by linarith
  rw [ha2_subst]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]