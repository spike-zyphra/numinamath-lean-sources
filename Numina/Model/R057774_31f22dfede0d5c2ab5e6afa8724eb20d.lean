import Mathlib

theorem algebra_4991 {a b x : ℝ} (ha : (2 * a - 5) ^ 2 + (b + 4) ^ 2 = 0) (hb : a * x - 3 * b = 7) :
    x = -2 := by
  have h1 : (2 * a - 5) ^ 2 = 0 := by
    linarith [sq_nonneg (2 * a - 5), sq_nonneg (b + 4)]
  have h2 : 2 * a - 5 = 0 := by
    rwa [sq_eq_zero_iff] at h1
  have ha_val : a = 5 / 2 := by
    linarith
  have h3 : (b + 4) ^ 2 = 0 := by
    linarith [sq_nonneg (2 * a - 5), sq_nonneg (b + 4)]
  have h4 : b + 4 = 0 := by
    rwa [sq_eq_zero_iff] at h3
  have hb_val : b = -4 := by
    linarith
  rw [ha_val, hb_val] at hb
  linarith