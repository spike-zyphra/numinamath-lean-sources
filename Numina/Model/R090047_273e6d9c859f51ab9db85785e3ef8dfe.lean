import Mathlib

theorem algebra_103857 {a b c : ℝ} (ha : a * b * c = (a + 1) * (b + 1) * (c + 1) - 1)
    (hb : a * b * c = (a + 2) * (b + 2) * (c + 2) - 2) :
    a = -1 ∧ b = -1 ∧ c = -1 := by
  have eq1 : a * b + a * c + b * c + a + b + c = 0 := by
    nlinarith
  have eq2 : 2 * a * b + 2 * a * c + 2 * b * c + 4 * a + 4 * b + 4 * c = -6 := by
    nlinarith
  have heq3 : a + b + c = -3 := by 
    nlinarith [eq1, eq2]
  have ha1 : (a + 1) ^ 2 + (b + 1) ^ 2 + (c + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have ha2 : (a + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
  have hb2 : (b + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
  have hc2 : (c + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
  have ha3 : a + 1 = 0 := by
    rwa [sq_eq_zero_iff] at ha2
  have hb3 : b + 1 = 0 := by
    rwa [sq_eq_zero_iff] at hb2
  have hc3 : c + 1 = 0 := by
    rwa [sq_eq_zero_iff] at hc2
  constructor
  · linarith
  constructor
  · linarith
  · linarith