import Mathlib

theorem algebra_362  {a : ℝ} (h : a^5 + a + 1 = 0) : a^3 - a^2 = -1 := by
  have h1 : a^5 + a + 1 = (a^2 + a + 1) * (a^3 - a^2 + 1) := by 
    ring
  have h2 : a^2 + a + 1 > 0 := by 
    nlinarith [sq_nonneg (a + 1 / 2)]
  have h3 : (a^2 + a + 1) * (a^3 - a^2 + 1) = 0 := by
    rw [←h1, h]
    all_goals nlinarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case 1: h4 : a^2 + a + 1 = 0
    linarith [h2]
  · -- Case 2: h5 : a^3 - a^2 + 1 = 0
    linarith [h5]