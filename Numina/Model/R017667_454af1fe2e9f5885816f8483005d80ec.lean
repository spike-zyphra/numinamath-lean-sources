import Mathlib

theorem algebra_5910 (x : ℝ) (y : ℕ) (hy : y > 0) (h1 : x^2 + 3 * y = 55) (h2 : 3 * x^2 * y + 6 * y^2 = 612) :
    y = 4 := by
  have eq1 : x^2 = (55 : ℝ) - 3 * (y : ℝ) := by
    linarith
  rw [eq1] at h2
  have h4 : (y : ℝ) > 0 := by
    exact_mod_cast (show (y : ℕ) > 0 by linarith)
  have h5 : 3 * ((y : ℝ) ) ^ 2 - 165 * (y : ℝ) + 612 = 0 := by
    nlinarith
  have h6 : ((y : ℝ) - 4) * ((y : ℝ) - 51) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- y - 4 = 0
    have h8 : (y : ℝ) = 4 := by linarith
    have h9 : y = 4 := by
      exact_mod_cast h8
    exact_mod_cast h9
  · -- y - 51 = 0
    -- Then, x^2 is invalid (negative)
    have h8 : (y : ℝ) = 51 := by linarith
    have h9 : y = 51 := by
      exact_mod_cast h8
    -- Check the first equation with y = 51
    -- x^2 = 55 - 3 * 51
    -- x^2 = 55 - 153 = -98
    -- This is a contradiction because x^2 >= 0
    have h10 : x^2 = (55 : ℝ) - 3 * (y : ℝ) := by
      linarith
    rw [show (y : ℝ) = 51 by linarith] at h10
    nlinarith [sq_nonneg x]