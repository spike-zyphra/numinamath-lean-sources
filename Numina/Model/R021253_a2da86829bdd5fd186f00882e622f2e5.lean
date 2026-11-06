import Mathlib

theorem algebra_1011 {a b : ℝ} (h : a ^ 5 - a ^ 4 * b - a ^ 4 + a - b - 1 = 0) (h' : 2 * a - 3 * b = 1) :
    a ^ 3 + b ^ 3 = 9 := by
  have eq1 : b = (2 * a - 1) / 3 := by
    linarith 
  rw [eq1] at h
  have eq3 : (a - 2) * (a^4 + 1) = 0 := by
    nlinarith [sq_nonneg (a ^ 2 - 2), sq_nonneg (a ^ 2), sq_nonneg (a - 2), sq_nonneg (a + 1), sq_nonneg (a - 1), sq_nonneg (a ^ 2 - 1)]
  cases' (mul_eq_zero.mp eq3) with h4 h5
  · -- a - 2 = 0, so a = 2
    have ha : a = 2 := by linarith
    have hb : b = 1 := by 
      rw [ha] at eq1
      linarith
    rw [ha, hb]
    norm_num
  · -- a^4 + 1 = 0, so a^4 = -1, which is impossible
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a + 1), sq_nonneg (a - 1), sq_nonneg (a ^ 4), sq_nonneg (a ^ 2 - 1)]